import NetHack.Soko22Hazard87.EqIntroBlocks0062
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro15750 (p : Pattern) (selected : d171923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d171899 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d171899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15746 q selected
    | true =>
      simp only [d171899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15747 q selected
  have h2 (q : Pattern) (selected : d171900 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d171900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d171901 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d171901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d171908 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d171908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15747 q selected
    | true =>
      simp only [d171908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15748 q selected
  have h5 (q : Pattern) (selected : d171909 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d171909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d171910 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d171910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d171911 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d171911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d171911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d171918 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d171918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15747 q selected
    | true =>
      simp only [d171918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15749 q selected
  have h9 (q : Pattern) (selected : d171919 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d171919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d171920 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d171920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d171921 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d171921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d171921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d171922 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d171922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d171923 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d171923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro15751 (p : Pattern) (selected : d171927 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d171918 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d171918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15747 q selected
    | true =>
      simp only [d171918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15749 q selected
  have h2 (q : Pattern) (selected : d171919 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d171919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d171920 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d171920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d171921 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d171921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d171921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d171926 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d171926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d171927 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d171927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d171927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15752 (p : Pattern) (selected : d171933 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d171924 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15750 q selected
    | true =>
      simp only [d171924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d171925 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d171928 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15751 q selected
    | true =>
      simp only [d171928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d171929 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d171930 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d171930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d171931 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d171931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d171932 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d171932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d171933 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d171933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15753 (p : Pattern) (selected : d171937 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d171928 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d171928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15751 q selected
    | true =>
      simp only [d171928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d171929 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d171929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d171934 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d171934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d171934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d171935 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d171935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d171935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d171936 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d171936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d171936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d171937 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d171937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d171937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15754 (p : Pattern) (selected : d171958 p = 1) : d173426 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d171868 q = 1) : d171868 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d171938 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d171938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15752 q selected
    | true =>
      simp only [d171938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15753 q selected
  have h3 (q : Pattern) (selected : d171939 q = 1) : d173422 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d171939, d173422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d171939, d173422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d171954 q = 1) : d171954 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d171955 q = 1) : d173423 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d171955, d173423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d171955, d173423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d171956 q = 1) : d173424 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d171956, d173424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171956, d173424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d171957 q = 1) : d173425 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d171957, d173425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171957, d173425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d171958 q = 1) : d173426 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d171958, d173426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171958, d173426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15755 (p : Pattern) (selected : d171975 p = 1) : d173432 p = 1 := by
  have h0 (q : Pattern) (selected : d171549 q = 1) : d171549 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d171743 q = 1) : d173410 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171743, d173410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15741 q selected
    | true =>
      simp only [d171743, d173410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15744 q selected
  have h2 (q : Pattern) (selected : d171761 q = 1) : d171761 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d171762 q = 1) : d173411 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171762, d173411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d171762, d173411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d171763 q = 1) : d173412 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171763, d173412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d171763, d173412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d171764 q = 1) : d173413 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171764, d173413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171764, d173413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d171768 q = 1) : d173417 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171768, d173417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d171768, d173417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15745 q selected
  have h8 (q : Pattern) (selected : d171770 q = 1) : d171770 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d171771 q = 1) : d173418 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171771, d173418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d171771, d173418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d171772 q = 1) : d173419 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171772, d173419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d171772, d173419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d171773 q = 1) : d173420 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171773, d173420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d171773, d173420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d171774 q = 1) : d173421 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171774, d173421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d171774, d173421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d171959 q = 1) : d173427 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d171959, d173427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d171959, d173427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15754 q selected
  have h14 (q : Pattern) (selected : d171970 q = 1) : d171970 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d171971 q = 1) : d173428 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d171971, d173428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d171971, d173428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d171972 q = 1) : d173429 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d171972, d173429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d171972, d173429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d171973 q = 1) : d173430 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d171973, d173430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d171973, d173430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d171974 q = 1) : d173431 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d171974, d173431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d171974, d173431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d171975 q = 1) : d173432 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d171975, d173432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d171975, d173432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro15756 (p : Pattern) (selected : d171981 p = 1) : d173438 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d171976 q = 1) : d173433 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d171976, d173433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171976, d173433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15755 q selected
  have h2 (q : Pattern) (selected : d171977 q = 1) : d173434 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d171977, d173434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171977, d173434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d171978 q = 1) : d173435 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d171978, d173435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171978, d173435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d171979 q = 1) : d173436 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d171979, d173436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171979, d173436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d171980 q = 1) : d173437 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d171980, d173437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171980, d173437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d171981 q = 1) : d173438 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d171981, d173438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171981, d173438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15757 (p : Pattern) (selected : d172156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2174 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro143 q selected
  have h2 (q : Pattern) (selected : d172152 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d172152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d172153 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d172153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2190 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro146 q selected
  have h5 (q : Pattern) (selected : d172154 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d172154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d172155 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d172155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d172156 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d172156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15758 (p : Pattern) (selected : d172161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2174 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro143 q selected
  have h2 (q : Pattern) (selected : d2190 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro146 q selected
  have h3 (q : Pattern) (selected : d172154 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d172154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d172155 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d172155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172161 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d172161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro15759 (p : Pattern) (selected : d172169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2174 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro143 q selected
  have h2 (q : Pattern) (selected : d172167 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d172167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d172168 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d172168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d172169 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d172169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro15760 (p : Pattern) (selected : d172176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2190 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro146 q selected
  have h2 (q : Pattern) (selected : d172174 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d172174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d172175 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d172175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d172176 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d172176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro15761 (p : Pattern) (selected : d172182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172157 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15757 q selected
    | true =>
      simp only [d172157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d172158 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d172159 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d172160 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d172160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172162 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15758 q selected
    | true =>
      simp only [d172162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d172163 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d172164 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d172165 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d172165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d172165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d172166 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d172166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d172170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15759 q selected
    | true =>
      simp only [d172170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d172171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d172171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d172172 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d172173 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d172173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d172173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d172177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15760 q selected
    | true =>
      simp only [d172177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d172178 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d172178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d172179 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d172180 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d172180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d172180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d172181 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d172181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d172181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d172182 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d172182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d172182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro15762 (p : Pattern) (selected : d172185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2174 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro143 q selected
  have h2 (q : Pattern) (selected : d2190 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro146 q selected
  have h3 (q : Pattern) (selected : d172154 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d172154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d172155 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d172155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2209 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro151 q selected
  have h6 (q : Pattern) (selected : d172183 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d172183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d172184 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d172184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d172184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d172185 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d172185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15763 (p : Pattern) (selected : d172190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2190 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro146 q selected
  have h2 (q : Pattern) (selected : d2209 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro151 q selected
  have h3 (q : Pattern) (selected : d172183 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d172183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d172184 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d172184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172190 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d172190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro15764 (p : Pattern) (selected : d172197 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172186 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15762 q selected
    | true =>
      simp only [d172186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d172187 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d172188 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d172189 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d172189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172191 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15763 q selected
    | true =>
      simp only [d172191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d172192 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d172193 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d172194 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d172194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d172194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d172195 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d172195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d172177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15760 q selected
    | true =>
      simp only [d172177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d172178 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d172178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d172179 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d172180 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d172180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d172180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d172196 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d172196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d172196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d172197 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d172197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d172197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro15765 (p : Pattern) (selected : d172204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2209 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro151 q selected
  have h2 (q : Pattern) (selected : d172201 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d172201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10515 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro151 q selected
    | true =>
      simp only [d10515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d172202 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d172202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172203 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d172203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d172204 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d172204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15766 (p : Pattern) (selected : d172210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15760 q selected
    | true =>
      simp only [d172177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d172178 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d172179 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d172180 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d172180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172196 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d172196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d172205 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15765 q selected
    | true =>
      simp only [d172205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d172206 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d172206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d172207 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d172208 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d172208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d172208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d172209 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d172209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d172209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d172210 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d172210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15767 (p : Pattern) (selected : d172216 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2190 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro146 q selected
  have h2 (q : Pattern) (selected : d2209 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro151 q selected
  have h3 (q : Pattern) (selected : d172183 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d172183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d172184 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d172184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172201 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d172201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d172215 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d172215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d172216 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d172216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15768 (p : Pattern) (selected : d172222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172217 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15767 q selected
    | true =>
      simp only [d172217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d172218 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d172219 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d172220 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d172220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172221 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d172221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d172205 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15765 q selected
    | true =>
      simp only [d172205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d172206 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d172206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d172207 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d172208 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d172208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d172208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d172209 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d172209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d172209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d172222 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d172222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15769 (p : Pattern) (selected : d172228 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172198 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d172198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15761 q selected
    | true =>
      simp only [d172198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15764 q selected
  have h2 (q : Pattern) (selected : d172199 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d172199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d172200 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d172200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d172211 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d172211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15764 q selected
    | true =>
      simp only [d172211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15766 q selected
  have h5 (q : Pattern) (selected : d172212 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d172212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d172213 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d172213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d172214 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d172214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d172223 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d172223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15764 q selected
    | true =>
      simp only [d172223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15768 q selected
  have h9 (q : Pattern) (selected : d172224 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d172224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d172225 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d172225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d172226 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d172226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d172226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d172227 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d172227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d172227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d172228 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d172228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d172228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro15770 (p : Pattern) (selected : d172232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172223 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d172223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15764 q selected
    | true =>
      simp only [d172223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15768 q selected
  have h2 (q : Pattern) (selected : d172224 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d172224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d172225 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d172225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d172226 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d172226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172231 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d172231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d172232 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d172232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15771 (p : Pattern) (selected : d172238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d172229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15769 q selected
    | true =>
      simp only [d172229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d172230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d172230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d172233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d172233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15770 q selected
    | true =>
      simp only [d172233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d172234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d172234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d172235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d172235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d172236 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d172236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d172237 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d172237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d172237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d172238 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d172238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15772 (p : Pattern) (selected : d172242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d172233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15770 q selected
    | true =>
      simp only [d172233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d172234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d172234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d172239 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d172239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d172240 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d172240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172241 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d172241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d172242 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d172242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15773 (p : Pattern) (selected : d172263 p = 1) : d173447 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172103 q = 1) : d172103 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d172112 q = 1) : d172112 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d172151 q = 1) : d172151 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d172243 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d172243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15771 q selected
    | true =>
      simp only [d172243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15772 q selected
  have h5 (q : Pattern) (selected : d172244 q = 1) : d173443 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d172244, d173443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172244, d173443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d172259 q = 1) : d172259 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d172260 q = 1) : d173444 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d172260, d173444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172260, d173444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d172261 q = 1) : d173445 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d172261, d173445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172261, d173445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d172262 q = 1) : d173446 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d172262, d173446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172262, d173446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d172263 q = 1) : d173447 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d172263, d173447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172263, d173447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro15774 (p : Pattern) (selected : d172278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d172229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15769 q selected
    | true =>
      simp only [d172229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d172230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d172230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d172233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d172233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15770 q selected
    | true =>
      simp only [d172233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d172234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d172234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d172235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d172235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d172236 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d172236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d172237 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d172237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d172237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d172278 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d172278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d172278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15775 (p : Pattern) (selected : d172279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d172233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15770 q selected
    | true =>
      simp only [d172233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d172234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d172234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d172239 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d172239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d172240 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d172240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172241 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d172241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d172279 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d172279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15776 (p : Pattern) (selected : d172288 p = 1) : d173452 p = 1 := by
  have h0 (q : Pattern) (selected : d172103 q = 1) : d172103 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172112 q = 1) : d172112 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d172151 q = 1) : d172151 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d172243 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d172243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15771 q selected
    | true =>
      simp only [d172243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15772 q selected
  have h4 (q : Pattern) (selected : d172244 q = 1) : d173443 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d172244, d173443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172244, d173443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d172259 q = 1) : d172259 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d172260 q = 1) : d173444 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d172260, d173444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172260, d173444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d172261 q = 1) : d173445 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d172261, d173445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172261, d173445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d172262 q = 1) : d173446 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d172262, d173446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172262, d173446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d172269 q = 1) : d172269 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d172274 q = 1) : d172274 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d172277 q = 1) : d172277 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d172280 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d172280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15774 q selected
    | true =>
      simp only [d172280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15775 q selected
  have h13 (q : Pattern) (selected : d172281 q = 1) : d173448 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d172281, d173448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d172281, d173448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d172284 q = 1) : d172284 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d172285 q = 1) : d173449 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d172285, d173449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d172285, d173449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d172286 q = 1) : d173450 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d172286, d173450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d172286, d173450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d172287 q = 1) : d173451 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d172287, d173451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d172287, d173451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d172288 q = 1) : d173452 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d172288, d173452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d172288, d173452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro15777 (p : Pattern) (selected : d172313 p = 1) : d173459 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172277 q = 1) : d172277 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d172280 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d172280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15774 q selected
    | true =>
      simp only [d172280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15775 q selected
  have h3 (q : Pattern) (selected : d172281 q = 1) : d173448 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d172281, d173448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172281, d173448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d172284 q = 1) : d172284 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d172285 q = 1) : d173449 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d172285, d173449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172285, d173449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d172311 q = 1) : d173457 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d172311, d173457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172311, d173457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d172312 q = 1) : d173458 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d172312, d173458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172312, d173458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d172313 q = 1) : d173459 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d172313, d173459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172313, d173459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15778 (p : Pattern) (selected : d172433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172415 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15757 q selected
  have h2 (q : Pattern) (selected : d172157 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15757 q selected
    | true =>
      simp only [d172157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d172416 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d172158 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172417 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d172418 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d172418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d172419 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15758 q selected
  have h8 (q : Pattern) (selected : d172162 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15758 q selected
    | true =>
      simp only [d172162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d172420 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d172420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d172163 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d172163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d172421 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d172421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d172422 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d172422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d172422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d172423 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d172423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d172423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d172424 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15759 q selected
  have h15 (q : Pattern) (selected : d172170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15759 q selected
    | true =>
      simp only [d172170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d172425 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d172425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d172171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d172171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d172426 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d172426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d172427 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d172427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d172427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d172428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15760 q selected
  have h21 (q : Pattern) (selected : d172177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15760 q selected
    | true =>
      simp only [d172177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d172429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d172429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d172178 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d172178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d172430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d172430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d172431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d172431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d172431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d172432 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d172432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d172432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d172433 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d172433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d172433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro15779 (p : Pattern) (selected : d172444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172434 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15762 q selected
  have h2 (q : Pattern) (selected : d172186 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15762 q selected
    | true =>
      simp only [d172186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d172435 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d172187 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172436 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d172437 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d172437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d172438 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15763 q selected
  have h8 (q : Pattern) (selected : d172191 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15763 q selected
    | true =>
      simp only [d172191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d172439 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d172439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d172192 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d172192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d172440 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d172440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d172441 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d172441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d172441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d172442 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d172442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d172442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d172428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15760 q selected
  have h15 (q : Pattern) (selected : d172177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15760 q selected
    | true =>
      simp only [d172177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d172429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d172429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d172178 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d172178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d172430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d172430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d172431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d172431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d172431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d172443 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d172443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d172443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d172444 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d172444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d172444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro15780 (p : Pattern) (selected : d172453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15760 q selected
  have h2 (q : Pattern) (selected : d172177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15760 q selected
    | true =>
      simp only [d172177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d172429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d172178 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d172431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d172431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d172443 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d172443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d172443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d172448 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15765 q selected
  have h9 (q : Pattern) (selected : d172205 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15765 q selected
    | true =>
      simp only [d172205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d172449 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d172449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d172206 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d172206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d172450 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d172450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d172451 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d172451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d172451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d172452 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d172452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d172452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d172453 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d172453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d172453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro15781 (p : Pattern) (selected : d172463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172458 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15767 q selected
  have h2 (q : Pattern) (selected : d172217 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15767 q selected
    | true =>
      simp only [d172217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d172459 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d172218 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172460 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d172461 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d172461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d172462 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d172462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d172462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d172448 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15765 q selected
  have h9 (q : Pattern) (selected : d172205 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d172205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15765 q selected
    | true =>
      simp only [d172205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d172449 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d172449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d172206 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d172206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d172206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d172450 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d172450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d172451 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d172451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d172451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d172452 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d172452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d172452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d172463 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d172463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d172463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro15782 (p : Pattern) (selected : d172469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172445 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d172445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15778 q selected
    | true =>
      simp only [d172445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15779 q selected
  have h2 (q : Pattern) (selected : d172446 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d172446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d172447 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d172447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d172454 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d172454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15779 q selected
    | true =>
      simp only [d172454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15780 q selected
  have h5 (q : Pattern) (selected : d172455 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d172455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d172456 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d172456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d172457 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d172457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d172464 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d172464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15779 q selected
    | true =>
      simp only [d172464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15781 q selected
  have h9 (q : Pattern) (selected : d172465 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d172465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d172466 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d172466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d172467 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d172467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d172467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d172468 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d172468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d172468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d172469 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d172469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d172469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro15783 (p : Pattern) (selected : d172473 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172464 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d172464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15779 q selected
    | true =>
      simp only [d172464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15781 q selected
  have h2 (q : Pattern) (selected : d172465 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d172465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d172466 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d172466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d172467 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d172467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d172472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d172473 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d172473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15784 (p : Pattern) (selected : d172479 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172470 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d172470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15782 q selected
    | true =>
      simp only [d172470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d172471 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d172471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d172474 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d172474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15783 q selected
    | true =>
      simp only [d172474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d172475 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d172475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d172476 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d172476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d172477 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d172477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d172478 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d172478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d172478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d172479 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d172479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d172479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15785 (p : Pattern) (selected : d172483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172474 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d172474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15783 q selected
    | true =>
      simp only [d172474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d172475 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d172475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d172480 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d172480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d172481 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d172481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172482 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d172482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d172483 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d172483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15786 (p : Pattern) (selected : d172504 p = 1) : d173469 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172414 q = 1) : d172414 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d172484 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d172484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15784 q selected
    | true =>
      simp only [d172484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15785 q selected
  have h3 (q : Pattern) (selected : d172485 q = 1) : d173465 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d172485, d173465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172485, d173465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d172500 q = 1) : d172500 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d172501 q = 1) : d173466 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d172501, d173466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172501, d173466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d172502 q = 1) : d173467 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d172502, d173467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172502, d173467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d172503 q = 1) : d173468 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d172503, d173468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172503, d173468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d172504 q = 1) : d173469 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d172504, d173469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172504, d173469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15787 (p : Pattern) (selected : d172521 p = 1) : d173475 p = 1 := by
  have h0 (q : Pattern) (selected : d172095 q = 1) : d172095 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172289 q = 1) : d173453 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d172289, d173453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15773 q selected
    | true =>
      simp only [d172289, d173453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15776 q selected
  have h2 (q : Pattern) (selected : d172307 q = 1) : d172307 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d172308 q = 1) : d173454 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d172308, d173454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172308, d173454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d172309 q = 1) : d173455 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d172309, d173455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172309, d173455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d172310 q = 1) : d173456 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d172310, d173456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172310, d173456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d172314 q = 1) : d173460 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d172314, d173460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172314, d173460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15777 q selected
  have h8 (q : Pattern) (selected : d172316 q = 1) : d172316 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d172317 q = 1) : d173461 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d172317, d173461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d172317, d173461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d172318 q = 1) : d173462 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d172318, d173462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d172318, d173462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d172319 q = 1) : d173463 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d172319, d173463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d172319, d173463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d172320 q = 1) : d173464 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d172320, d173464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d172320, d173464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d172505 q = 1) : d173470 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d172505, d173470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172505, d173470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15786 q selected
  have h14 (q : Pattern) (selected : d172516 q = 1) : d172516 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d172517 q = 1) : d173471 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d172517, d173471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d172517, d173471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d172518 q = 1) : d173472 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d172518, d173472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d172518, d173472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d172519 q = 1) : d173473 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d172519, d173473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d172519, d173473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d172520 q = 1) : d173474 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d172520, d173474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d172520, d173474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d172521 q = 1) : d173475 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d172521, d173475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d172521, d173475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro15788 (p : Pattern) (selected : d172527 p = 1) : d173481 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172522 q = 1) : d173476 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d172522, d173476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172522, d173476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15787 q selected
  have h2 (q : Pattern) (selected : d172523 q = 1) : d173477 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d172523, d173477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172523, d173477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d172524 q = 1) : d173478 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d172524, d173478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172524, d173478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d172525 q = 1) : d173479 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d172525, d173479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172525, d173479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d172526 q = 1) : d173480 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d172526, d173480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172526, d173480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d172527 q = 1) : d173481 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d172527, d173481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172527, d173481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15789 (p : Pattern) (selected : d172533 p = 1) : d173487 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d171982 q = 1) : d173439 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d171982, d173439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171982, d173439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15756 q selected
  have h2 (q : Pattern) (selected : d171983 q = 1) : d173440 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d171983, d173440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171983, d173440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d171984 q = 1) : d173441 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d171984, d173441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171984, d173441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d171985 q = 1) : d173442 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d171985, d173442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d171985, d173442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d172528 q = 1) : d173482 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d172528, d173482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172528, d173482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15788 q selected
  have h6 (q : Pattern) (selected : d172529 q = 1) : d173483 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d172529, d173483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172529, d173483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d172530 q = 1) : d173484 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d172530, d173484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172530, d173484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d172531 q = 1) : d173485 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d172531, d173485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172531, d173485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d172532 q = 1) : d173486 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d172532, d173486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172532, d173486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d172533 q = 1) : d173487 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d172533, d173487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d172533, d173487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15790 (p : Pattern) (selected : d172539 p = 1) : d173493 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172534 q = 1) : d173488 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d172534, d173488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15789 q selected
    | true =>
      simp only [d172534, d173488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d172535 q = 1) : d173489 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d172535, d173489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172535, d173489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d172536 q = 1) : d173490 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d172536, d173490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172536, d173490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d172537 q = 1) : d173491 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d172537, d173491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172537, d173491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172538 q = 1) : d173492 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d172538, d173492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172538, d173492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d172539 q = 1) : d173493 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d172539, d173493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172539, d173493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15791 (p : Pattern) (selected : d172545 p = 1) : d173499 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172540 q = 1) : d173494 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d172540, d173494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15790 q selected
    | true =>
      simp only [d172540, d173494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d172541 q = 1) : d173495 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d172541, d173495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172541, d173495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d172542 q = 1) : d173496 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d172542, d173496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172542, d173496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d172543 q = 1) : d173497 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d172543, d173497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172543, d173497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172544 q = 1) : d173498 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d172544, d173498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172544, d173498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d172545 q = 1) : d173499 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d172545, d173499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172545, d173499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15792 (p : Pattern) (selected : d172551 p = 1) : d173505 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172546 q = 1) : d173500 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d172546, d173500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15791 q selected
    | true =>
      simp only [d172546, d173500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d172547 q = 1) : d173501 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d172547, d173501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172547, d173501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d172548 q = 1) : d173502 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d172548, d173502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172548, d173502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d172549 q = 1) : d173503 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d172549, d173503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172549, d173503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172550 q = 1) : d173504 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d172550, d173504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172550, d173504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d172551 q = 1) : d173505 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d172551, d173505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172551, d173505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15793 (p : Pattern) (selected : d172557 p = 1) : d173511 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172552 q = 1) : d173506 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d172552, d173506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15792 q selected
    | true =>
      simp only [d172552, d173506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d172553 q = 1) : d173507 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d172553, d173507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172553, d173507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d172554 q = 1) : d173508 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d172554, d173508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172554, d173508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d172555 q = 1) : d173509 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d172555, d173509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172555, d173509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172556 q = 1) : d173510 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d172556, d173510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172556, d173510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d172557 q = 1) : d173511 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d172557, d173511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172557, d173511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15794 (p : Pattern) (selected : d172563 p = 1) : d173517 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172558 q = 1) : d173512 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d172558, d173512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15793 q selected
    | true =>
      simp only [d172558, d173512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d172559 q = 1) : d173513 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d172559, d173513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172559, d173513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d172560 q = 1) : d173514 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d172560, d173514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172560, d173514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d172561 q = 1) : d173515 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d172561, d173515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172561, d173515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172562 q = 1) : d173516 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d172562, d173516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172562, d173516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d172563 q = 1) : d173517 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d172563, d173517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172563, d173517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15795 (p : Pattern) (selected : d172569 p = 1) : d173523 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172564 q = 1) : d173518 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d172564, d173518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15794 q selected
    | true =>
      simp only [d172564, d173518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d172565 q = 1) : d173519 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d172565, d173519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172565, d173519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d172566 q = 1) : d173520 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d172566, d173520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172566, d173520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d172567 q = 1) : d173521 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d172567, d173521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172567, d173521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172568 q = 1) : d173522 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d172568, d173522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172568, d173522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d172569 q = 1) : d173523 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d172569, d173523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172569, d173523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15796 (p : Pattern) (selected : d172575 p = 1) : d173529 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d172570 q = 1) : d173524 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d172570, d173524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15795 q selected
    | true =>
      simp only [d172570, d173524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d172571 q = 1) : d173525 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d172571, d173525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d172571, d173525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d172572 q = 1) : d173526 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d172572, d173526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d172572, d173526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d172573 q = 1) : d173527 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d172573, d173527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d172573, d173527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d172574 q = 1) : d173528 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d172574, d173528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d172574, d173528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d172575 q = 1) : d173529 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d172575, d173529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d172575, d173529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15797 (p : Pattern) (selected : d173758 p = 0) : d174650 p = 1 := by
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
  have h2 (q : Pattern) (selected : d173756 q = 0) : d174648 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173756, d174648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173756, d174648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d173757 q = 0) : d174649 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d173757, d174649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173757, d174649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173758 q = 0) : d174650 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d173758, d174650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173758, d174650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro15798 (p : Pattern) (selected : d173764 p = 0) : d174656 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173759 q = 0) : d174651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173759, d174651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15797 q selected
    | true =>
      simp only [d173759, d174651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173760 q = 0) : d174652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173760, d174652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173760, d174652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173761 q = 0) : d174653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173761, d174653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173761, d174653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173762 q = 0) : d174654 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173762, d174654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173762, d174654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173763 q = 0) : d174655 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173763, d174655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173763, d174655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173764 q = 0) : d174656 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173764, d174656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173764, d174656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15799 (p : Pattern) (selected : d173770 p = 0) : d174662 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173765 q = 0) : d174657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173765, d174657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15798 q selected
    | true =>
      simp only [d173765, d174657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173766 q = 0) : d174658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173766, d174658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173766, d174658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173767 q = 0) : d174659 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173767, d174659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173767, d174659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173768 q = 0) : d174660 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173768, d174660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173768, d174660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173769 q = 0) : d174661 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173769, d174661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173769, d174661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173770 q = 0) : d174662 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173770, d174662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173770, d174662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15800 (p : Pattern) (selected : d173776 p = 0) : d174668 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173771 q = 0) : d174663 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173771, d174663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15799 q selected
    | true =>
      simp only [d173771, d174663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173772 q = 0) : d174664 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173772, d174664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173772, d174664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d173773 q = 0) : d174665 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173773, d174665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173773, d174665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173774 q = 0) : d174666 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173774, d174666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173774, d174666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d173775 q = 0) : d174667 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173775, d174667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173775, d174667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173776 q = 0) : d174668 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173776, d174668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173776, d174668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15801 (p : Pattern) (selected : d173782 p = 0) : d174674 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173777 q = 0) : d174669 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173777, d174669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173777, d174669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15800 q selected
  have h2 (q : Pattern) (selected : d173778 q = 0) : d174670 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173778, d174670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173778, d174670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d173779 q = 0) : d174671 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173779, d174671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173779, d174671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173780 q = 0) : d174672 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173780, d174672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173780, d174672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173781 q = 0) : d174673 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173781, d174673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173781, d174673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173782 q = 0) : d174674 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173782, d174674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173782, d174674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15802 (p : Pattern) (selected : d173789 p = 0) : d174681 p = 1 := by
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
  have h2 (q : Pattern) (selected : d173787 q = 0) : d174679 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173787, d174679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173787, d174679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173756 q = 0) : d174648 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173756, d174648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173756, d174648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173788 q = 0) : d174680 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d173788, d174680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173788, d174680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173757 q = 0) : d174649 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d173757, d174649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173757, d174649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d173789 q = 0) : d174681 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d173789, d174681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173789, d174681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15803 (p : Pattern) (selected : d173795 p = 0) : d174687 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173790 q = 0) : d174682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173790, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15802 q selected
    | true =>
      simp only [d173790, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15797 q selected
  have h2 (q : Pattern) (selected : d173791 q = 0) : d174683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173791, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173791, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173792 q = 0) : d174684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173792, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173792, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173759 q = 0) : d174651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173759, d174651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15797 q selected
    | true =>
      simp only [d173759, d174651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173760 q = 0) : d174652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173760, d174652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173760, d174652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173761 q = 0) : d174653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173761, d174653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173761, d174653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173793 q = 0) : d174685 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173793, d174685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173793, d174685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173762 q = 0) : d174654 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173762, d174654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173762, d174654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d173794 q = 0) : d174686 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173794, d174686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173794, d174686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d173795 q = 0) : d174687 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173795, d174687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d173795, d174687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15804 (p : Pattern) (selected : d173801 p = 0) : d174693 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173796 q = 0) : d174688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173796, d174688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15803 q selected
    | true =>
      simp only [d173796, d174688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173797 q = 0) : d174689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173797, d174689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173797, d174689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173765 q = 0) : d174657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173765, d174657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15798 q selected
    | true =>
      simp only [d173765, d174657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173766 q = 0) : d174658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173766, d174658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173766, d174658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d173798 q = 0) : d174690 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173798, d174690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173798, d174690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173799 q = 0) : d174691 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173799, d174691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173799, d174691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d173800 q = 0) : d174692 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173800, d174692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173800, d174692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d173801 q = 0) : d174693 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173801, d174693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173801, d174693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15805 (p : Pattern) (selected : d173805 p = 0) : d174650 p = 1 := by
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
  have h2 (q : Pattern) (selected : d173803 q = 0) : d174648 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173803, d174648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173803, d174648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d173804 q = 0) : d174649 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d173804, d174649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173804, d174649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173805 q = 0) : d174650 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d173805, d174650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173805, d174650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro15806 (p : Pattern) (selected : d173811 p = 0) : d174656 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173806 q = 0) : d174651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173806, d174651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15805 q selected
    | true =>
      simp only [d173806, d174651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173807 q = 0) : d174652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173807, d174652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173807, d174652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173808 q = 0) : d174653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173808, d174653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173808, d174653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173809 q = 0) : d174654 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173809, d174654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173809, d174654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173810 q = 0) : d174655 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173810, d174655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173810, d174655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173811 q = 0) : d174656 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173811, d174656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173811, d174656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15807 (p : Pattern) (selected : d173817 p = 0) : d174662 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173812 q = 0) : d174657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173812, d174657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15806 q selected
    | true =>
      simp only [d173812, d174657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173813 q = 0) : d174658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173813, d174658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173813, d174658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173814 q = 0) : d174659 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173814, d174659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173814, d174659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173815 q = 0) : d174660 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173815, d174660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173815, d174660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173816 q = 0) : d174661 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173816, d174661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173816, d174661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173817 q = 0) : d174662 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173817, d174662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173817, d174662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15808 (p : Pattern) (selected : d173823 p = 0) : d174699 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173802 q = 0) : d174694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173802, d174694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15804 q selected
    | true =>
      simp only [d173802, d174694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15799 q selected
  have h2 (q : Pattern) (selected : d173818 q = 0) : d174663 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173818, d174663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15807 q selected
    | true =>
      simp only [d173818, d174663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d173819 q = 0) : d174695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173819, d174695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173819, d174695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173771 q = 0) : d174663 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173771, d174663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15799 q selected
    | true =>
      simp only [d173771, d174663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173772 q = 0) : d174664 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173772, d174664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173772, d174664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173820 q = 0) : d174696 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173820, d174696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173820, d174696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173821 q = 0) : d174697 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173821, d174697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173821, d174697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173822 q = 0) : d174698 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173822, d174698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173822, d174698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d173823 q = 0) : d174699 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173823, d174699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173823, d174699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15809 (p : Pattern) (selected : d173829 p = 0) : d174705 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173824 q = 0) : d174700 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173824, d174700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173824, d174700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15808 q selected
  have h2 (q : Pattern) (selected : d173825 q = 0) : d174701 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173825, d174701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173825, d174701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d173826 q = 0) : d174702 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173826, d174702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173826, d174702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173827 q = 0) : d174703 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173827, d174703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173827, d174703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173828 q = 0) : d174704 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173828, d174704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173828, d174704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173829 q = 0) : d174705 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173829, d174705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173829, d174705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15810 (p : Pattern) (selected : d173839 p = 0) : d174715 p = 1 := by
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
  have h2 (q : Pattern) (selected : d173835 q = 0) : d174711 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173835, d174711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173835, d174711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d139 q = 0) : d51990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro205 q selected
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173787 q = 0) : d174679 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173787, d174679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173787, d174679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173836 q = 0) : d174712 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d173836, d174712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173836, d174712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9382 q = 0) : d101015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d173837 q = 0) : d174713 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173837, d174713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173837, d174713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
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
  have h9 (q : Pattern) (selected : d173756 q = 0) : d174648 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173756, d174648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d173756, d174648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d173838 q = 0) : d174714 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d173838, d174714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173838, d174714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d173839 q = 0) : d174715 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d173839, d174715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173839, d174715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15811 (p : Pattern) (selected : d173845 p = 0) : d174721 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173840 q = 0) : d174716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173840, d174716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15810 q selected
    | true =>
      simp only [d173840, d174716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15802 q selected
  have h2 (q : Pattern) (selected : d173841 q = 0) : d174717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173841, d174717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173841, d174717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173842 q = 0) : d174718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173842, d174718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173842, d174718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173790 q = 0) : d174682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173790, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15802 q selected
    | true =>
      simp only [d173790, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15797 q selected
  have h5 (q : Pattern) (selected : d173791 q = 0) : d174683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173791, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173791, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173792 q = 0) : d174684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173792, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173792, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173843 q = 0) : d174719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173843, d174719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173843, d174719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173759 q = 0) : d174651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173759, d174651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15797 q selected
    | true =>
      simp only [d173759, d174651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d173760 q = 0) : d174652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173760, d174652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173760, d174652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d173761 q = 0) : d174653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173761, d174653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173761, d174653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d173793 q = 0) : d174685 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173793, d174685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173793, d174685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d173844 q = 0) : d174720 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173844, d174720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173844, d174720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d173845 q = 0) : d174721 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173845, d174721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d173845, d174721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro15812 (p : Pattern) (selected : d173851 p = 0) : d174727 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173846 q = 0) : d174722 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173846, d174722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15811 q selected
    | true =>
      simp only [d173846, d174722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173847 q = 0) : d174723 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173847, d174723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173847, d174723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173796 q = 0) : d174688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173796, d174688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15803 q selected
    | true =>
      simp only [d173796, d174688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173797 q = 0) : d174689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173797, d174689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173797, d174689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d173848 q = 0) : d174724 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173848, d174724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173848, d174724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173849 q = 0) : d174725 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173849, d174725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173849, d174725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d173850 q = 0) : d174726 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173850, d174726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173850, d174726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d173851 q = 0) : d174727 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173851, d174727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173851, d174727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15813 (p : Pattern) (selected : d173855 p = 0) : d174681 p = 1 := by
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
  have h2 (q : Pattern) (selected : d173853 q = 0) : d174679 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173853, d174679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173853, d174679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d170 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
    | true =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173803 q = 0) : d174648 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173803, d174648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173803, d174648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173854 q = 0) : d174680 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d173854, d174680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173854, d174680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173804 q = 0) : d174649 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d173804, d174649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173804, d174649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d173855 q = 0) : d174681 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d173855, d174681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173855, d174681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15814 (p : Pattern) (selected : d173861 p = 0) : d174687 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173856 q = 0) : d174682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173856, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15813 q selected
    | true =>
      simp only [d173856, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15805 q selected
  have h2 (q : Pattern) (selected : d173857 q = 0) : d174683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173857, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173857, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173858 q = 0) : d174684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173858, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173858, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173806 q = 0) : d174651 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173806, d174651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15805 q selected
    | true =>
      simp only [d173806, d174651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173807 q = 0) : d174652 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173807, d174652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173807, d174652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173808 q = 0) : d174653 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173808, d174653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173808, d174653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173859 q = 0) : d174685 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173859, d174685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173859, d174685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173809 q = 0) : d174654 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173809, d174654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173809, d174654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d173860 q = 0) : d174686 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173860, d174686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173860, d174686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d173861 q = 0) : d174687 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173861, d174687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d173861, d174687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15815 (p : Pattern) (selected : d173867 p = 0) : d174693 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173862 q = 0) : d174688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173862, d174688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15814 q selected
    | true =>
      simp only [d173862, d174688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173863 q = 0) : d174689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173863, d174689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173863, d174689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173812 q = 0) : d174657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173812, d174657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15806 q selected
    | true =>
      simp only [d173812, d174657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173813 q = 0) : d174658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173813, d174658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173813, d174658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d173864 q = 0) : d174690 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173864, d174690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173864, d174690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173865 q = 0) : d174691 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173865, d174691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173865, d174691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d173866 q = 0) : d174692 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173866, d174692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173866, d174692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d173867 q = 0) : d174693 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173867, d174693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173867, d174693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15816 (p : Pattern) (selected : d173873 p = 0) : d174733 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173796 q = 0) : d174688 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173796, d174688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15803 q selected
    | true =>
      simp only [d173796, d174688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173797 q = 0) : d174689 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173797, d174689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173797, d174689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173870 q = 0) : d174730 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173870, d174730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173870, d174730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173871 q = 0) : d174731 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173871, d174731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173871, d174731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173872 q = 0) : d174732 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173872, d174732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173872, d174732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173873 q = 0) : d174733 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173873, d174733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173873, d174733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15817 (p : Pattern) (selected : d173879 p = 0) : d174739 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173852 q = 0) : d174728 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173852, d174728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15812 q selected
    | true =>
      simp only [d173852, d174728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15804 q selected
  have h2 (q : Pattern) (selected : d173868 q = 0) : d174694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173868, d174694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15815 q selected
    | true =>
      simp only [d173868, d174694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15807 q selected
  have h3 (q : Pattern) (selected : d173869 q = 0) : d174729 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173869, d174729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173869, d174729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173874 q = 0) : d174734 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173874, d174734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15816 q selected
    | true =>
      simp only [d173874, d174734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173875 q = 0) : d174735 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173875, d174735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173875, d174735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173876 q = 0) : d174736 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173876, d174736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173876, d174736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173877 q = 0) : d174737 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173877, d174737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173877, d174737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173878 q = 0) : d174738 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173878, d174738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173878, d174738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d173879 q = 0) : d174739 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173879, d174739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173879, d174739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15818 (p : Pattern) (selected : d173885 p = 0) : d174745 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173771 q = 0) : d174663 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173771, d174663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15799 q selected
    | true =>
      simp only [d173771, d174663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173881 q = 0) : d174741 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173881, d174741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173881, d174741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173882 q = 0) : d174742 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173882, d174742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173882, d174742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173883 q = 0) : d174743 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173883, d174743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173883, d174743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d173884 q = 0) : d174744 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173884, d174744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173884, d174744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173885 q = 0) : d174745 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173885, d174745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173885, d174745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15819 (p : Pattern) (selected : d173891 p = 0) : d174751 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173880 q = 0) : d174740 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173880, d174740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173880, d174740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15817 q selected
  have h2 (q : Pattern) (selected : d173886 q = 0) : d174746 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173886, d174746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173886, d174746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15818 q selected
  have h3 (q : Pattern) (selected : d173887 q = 0) : d174747 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173887, d174747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173887, d174747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173888 q = 0) : d174748 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173888, d174748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173888, d174748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173889 q = 0) : d174749 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173889, d174749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173889, d174749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173890 q = 0) : d174750 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173890, d174750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173890, d174750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d173891 q = 0) : d174751 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173891, d174751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173891, d174751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15820 (p : Pattern) (selected : d173897 p = 0) : d174757 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173783 q = 0) : d174675 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173783, d174675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173783, d174675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15801 q selected
  have h2 (q : Pattern) (selected : d173784 q = 0) : d174676 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173784, d174676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173784, d174676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173785 q = 0) : d174677 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173785, d174677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173785, d174677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173786 q = 0) : d174678 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173786, d174678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173786, d174678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d173830 q = 0) : d174706 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173830, d174706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173830, d174706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15809 q selected
  have h6 (q : Pattern) (selected : d173831 q = 0) : d174707 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173831, d174707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173831, d174707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173832 q = 0) : d174708 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173832, d174708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173832, d174708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173833 q = 0) : d174709 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173833, d174709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173833, d174709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d173834 q = 0) : d174710 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173834, d174710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173834, d174710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d173892 q = 0) : d174752 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173892, d174752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173892, d174752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15819 q selected
  have h11 (q : Pattern) (selected : d173893 q = 0) : d174753 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173893, d174753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173893, d174753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d173894 q = 0) : d174754 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173894, d174754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173894, d174754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d173895 q = 0) : d174755 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173895, d174755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173895, d174755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d173896 q = 0) : d174756 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173896, d174756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173896, d174756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d173897 q = 0) : d174757 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173897, d174757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d173897, d174757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro15821 (p : Pattern) (selected : d173903 p = 0) : d174763 p = 1 := by
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
  have h2 (q : Pattern) (selected : d173898 q = 0) : d174758 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173898, d174758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173898, d174758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9458 q = 0) : d101073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6619 q selected
    | true =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173899 q = 0) : d174759 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173899, d174759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173899, d174759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173900 q = 0) : d174760 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d173900, d174760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173900, d174760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9468 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d173901 q = 0) : d174761 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173901, d174761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173901, d174761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9382 q = 0) : d101015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d173837 q = 0) : d174713 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173837, d174713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d173837, d174713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d173902 q = 0) : d174762 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d173902, d174762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173902, d174762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d173903 q = 0) : d174763 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d173903, d174763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173903, d174763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15822 (p : Pattern) (selected : d173907 p = 0) : d174767 p = 1 := by
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
  have h2 (q : Pattern) (selected : d173837 q = 0) : d174713 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173837, d174713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173837, d174713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173756 q = 0) : d174648 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173756, d174648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173756, d174648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173838 q = 0) : d174714 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d173838, d174714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173838, d174714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173757 q = 0) : d174649 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d173757, d174649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173757, d174649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d173907 q = 0) : d174767 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d173907, d174767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173907, d174767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15823 (p : Pattern) (selected : d173913 p = 0) : d174773 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173904 q = 0) : d174764 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173904, d174764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15821 q selected
    | true =>
      simp only [d173904, d174764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15810 q selected
  have h2 (q : Pattern) (selected : d173905 q = 0) : d174765 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173905, d174765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173905, d174765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173906 q = 0) : d174766 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173906, d174766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173906, d174766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173908 q = 0) : d174768 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173908, d174768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15810 q selected
    | true =>
      simp only [d173908, d174768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15822 q selected
  have h5 (q : Pattern) (selected : d173909 q = 0) : d174769 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173909, d174769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173909, d174769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173910 q = 0) : d174770 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173910, d174770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173910, d174770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173911 q = 0) : d174771 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173911, d174771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173911, d174771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173840 q = 0) : d174716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173840, d174716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15810 q selected
    | true =>
      simp only [d173840, d174716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15802 q selected
  have h9 (q : Pattern) (selected : d173841 q = 0) : d174717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173841, d174717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173841, d174717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d173842 q = 0) : d174718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173842, d174718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173842, d174718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d173790 q = 0) : d174682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173790, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15802 q selected
    | true =>
      simp only [d173790, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15797 q selected
  have h12 (q : Pattern) (selected : d173791 q = 0) : d174683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173791, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173791, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d173792 q = 0) : d174684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173792, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173792, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d173843 q = 0) : d174719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173843, d174719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d173843, d174719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d173912 q = 0) : d174772 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173912, d174772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173912, d174772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d173913 q = 0) : d174773 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173913, d174773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d173913, d174773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro15824 (p : Pattern) (selected : d173918 p = 0) : d174778 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173840 q = 0) : d174716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173840, d174716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15810 q selected
    | true =>
      simp only [d173840, d174716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15802 q selected
  have h2 (q : Pattern) (selected : d173841 q = 0) : d174717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173841, d174717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173841, d174717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173842 q = 0) : d174718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173842, d174718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173842, d174718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173790 q = 0) : d174682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173790, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15802 q selected
    | true =>
      simp only [d173790, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15797 q selected
  have h5 (q : Pattern) (selected : d173791 q = 0) : d174683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173791, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173791, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173792 q = 0) : d174684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173792, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173792, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173843 q = 0) : d174719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173843, d174719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173843, d174719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173916 q = 0) : d174776 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173916, d174776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173916, d174776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d173917 q = 0) : d174777 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173917, d174777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173917, d174777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d173918 q = 0) : d174778 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173918, d174778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d173918, d174778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15825 (p : Pattern) (selected : d173924 p = 0) : d174784 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173914 q = 0) : d174774 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173914, d174774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15823 q selected
    | true =>
      simp only [d173914, d174774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173915 q = 0) : d174775 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173915, d174775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173915, d174775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173919 q = 0) : d174779 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173919, d174779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15824 q selected
    | true =>
      simp only [d173919, d174779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173920 q = 0) : d174780 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173920, d174780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173920, d174780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d173921 q = 0) : d174781 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173921, d174781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173921, d174781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173922 q = 0) : d174782 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173922, d174782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173922, d174782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d173923 q = 0) : d174783 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173923, d174783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173923, d174783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d173924 q = 0) : d174784 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173924, d174784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173924, d174784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15826 (p : Pattern) (selected : d173926 p = 0) : d174786 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173790 q = 0) : d174682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173790, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15802 q selected
    | true =>
      simp only [d173790, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15797 q selected
  have h2 (q : Pattern) (selected : d173791 q = 0) : d174683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173791, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173791, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173792 q = 0) : d174684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173792, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173792, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173916 q = 0) : d174776 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173916, d174776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173916, d174776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173925 q = 0) : d174785 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173925, d174785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173925, d174785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173926 q = 0) : d174786 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173926, d174786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173926, d174786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15827 (p : Pattern) (selected : d173932 p = 0) : d174792 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173919 q = 0) : d174779 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173919, d174779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15824 q selected
    | true =>
      simp only [d173919, d174779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173920 q = 0) : d174780 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173920, d174780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173920, d174780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173927 q = 0) : d174787 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173927, d174787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15826 q selected
    | true =>
      simp only [d173927, d174787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173928 q = 0) : d174788 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173928, d174788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173928, d174788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d173929 q = 0) : d174789 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173929, d174789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173929, d174789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173930 q = 0) : d174790 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173930, d174790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173930, d174790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d173931 q = 0) : d174791 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173931, d174791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173931, d174791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d173932 q = 0) : d174792 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173932, d174792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173932, d174792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15828 (p : Pattern) (selected : d173938 p = 0) : d174715 p = 1 := by
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
  have h2 (q : Pattern) (selected : d173934 q = 0) : d174711 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173934, d174711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173934, d174711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d350 q = 0) : d51990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro240 q selected
    | true =>
      simp only [d350, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173853 q = 0) : d174679 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173853, d174679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173853, d174679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173935 q = 0) : d174712 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d173935, d174712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173935, d174712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9512 q = 0) : d101015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9512, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6628 q selected
    | true =>
      simp only [d9512, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d173936 q = 0) : d174713 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173936, d174713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173936, d174713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d170 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
    | true =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d173803 q = 0) : d174648 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173803, d174648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d173803, d174648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d173937 q = 0) : d174714 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d173937, d174714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173937, d174714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d173938 q = 0) : d174715 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d173938, d174715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173938, d174715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15829 (p : Pattern) (selected : d173945 p = 0) : d174778 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173939 q = 0) : d174716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173939, d174716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15828 q selected
    | true =>
      simp only [d173939, d174716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15813 q selected
  have h2 (q : Pattern) (selected : d173940 q = 0) : d174717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173940, d174717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173940, d174717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173941 q = 0) : d174718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173941, d174718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173941, d174718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173856 q = 0) : d174682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173856, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15813 q selected
    | true =>
      simp only [d173856, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15805 q selected
  have h5 (q : Pattern) (selected : d173857 q = 0) : d174683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173857, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173857, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173858 q = 0) : d174684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173858, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173858, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173942 q = 0) : d174719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173942, d174719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173942, d174719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173943 q = 0) : d174776 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173943, d174776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173943, d174776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d173944 q = 0) : d174777 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173944, d174777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173944, d174777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d173945 q = 0) : d174778 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173945, d174778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d173945, d174778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15830 (p : Pattern) (selected : d173949 p = 0) : d174786 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173856 q = 0) : d174682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173856, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15813 q selected
    | true =>
      simp only [d173856, d174682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15805 q selected
  have h2 (q : Pattern) (selected : d173857 q = 0) : d174683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173857, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173857, d174683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173858 q = 0) : d174684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173858, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173858, d174684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173943 q = 0) : d174776 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173943, d174776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173943, d174776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173948 q = 0) : d174785 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173948, d174785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173948, d174785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173949 q = 0) : d174786 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173949, d174786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173949, d174786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15831 (p : Pattern) (selected : d173955 p = 0) : d174792 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173946 q = 0) : d174779 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173946, d174779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15829 q selected
    | true =>
      simp only [d173946, d174779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173947 q = 0) : d174780 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173947, d174780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173947, d174780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173950 q = 0) : d174787 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173950, d174787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15830 q selected
    | true =>
      simp only [d173950, d174787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173951 q = 0) : d174788 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173951, d174788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173951, d174788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d173952 q = 0) : d174789 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173952, d174789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173952, d174789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173953 q = 0) : d174790 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173953, d174790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173953, d174790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d173954 q = 0) : d174791 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173954, d174791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173954, d174791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d173955 q = 0) : d174792 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173955, d174792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173955, d174792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15832 (p : Pattern) (selected : d173959 p = 0) : d174797 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173950 q = 0) : d174787 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173950, d174787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15830 q selected
    | true =>
      simp only [d173950, d174787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173951 q = 0) : d174788 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173951, d174788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173951, d174788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173956 q = 0) : d174794 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173956, d174794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173956, d174794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173957 q = 0) : d174795 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173957, d174795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173957, d174795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173958 q = 0) : d174796 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173958, d174796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173958, d174796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173959 q = 0) : d174797 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173959, d174797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173959, d174797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15833 (p : Pattern) (selected : d173965 p = 0) : d174803 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173919 q = 0) : d174779 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173919, d174779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15824 q selected
    | true =>
      simp only [d173919, d174779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173920 q = 0) : d174780 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173920, d174780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173920, d174780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173962 q = 0) : d174800 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173962, d174800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173962, d174800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173963 q = 0) : d174801 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173963, d174801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173963, d174801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173964 q = 0) : d174802 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173964, d174802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173964, d174802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173965 q = 0) : d174803 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173965, d174803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173965, d174803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15834 (p : Pattern) (selected : d173971 p = 0) : d174809 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173933 q = 0) : d174793 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173933, d174793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15825 q selected
    | true =>
      simp only [d173933, d174793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15827 q selected
  have h2 (q : Pattern) (selected : d173960 q = 0) : d174798 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173960, d174798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15831 q selected
    | true =>
      simp only [d173960, d174798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15832 q selected
  have h3 (q : Pattern) (selected : d173961 q = 0) : d174799 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173961, d174799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173961, d174799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173966 q = 0) : d174804 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173966, d174804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15833 q selected
    | true =>
      simp only [d173966, d174804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173967 q = 0) : d174805 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173967, d174805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173967, d174805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173968 q = 0) : d174806 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173968, d174806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173968, d174806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173969 q = 0) : d174807 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173969, d174807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173969, d174807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173970 q = 0) : d174808 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173970, d174808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173970, d174808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d173971 q = 0) : d174809 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173971, d174809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173971, d174809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15835 (p : Pattern) (selected : d173976 p = 0) : d174797 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173927 q = 0) : d174787 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173927, d174787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15826 q selected
    | true =>
      simp only [d173927, d174787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173928 q = 0) : d174788 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173928, d174788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173928, d174788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173973 q = 0) : d174794 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173973, d174794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173973, d174794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173974 q = 0) : d174795 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173974, d174795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173974, d174795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173975 q = 0) : d174796 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173975, d174796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173975, d174796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173976 q = 0) : d174797 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173976, d174797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173976, d174797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15836 (p : Pattern) (selected : d173982 p = 0) : d174816 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173977 q = 0) : d174811 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173977, d174811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15835 q selected
    | true =>
      simp only [d173977, d174811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173978 q = 0) : d174812 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173978, d174812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173978, d174812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173979 q = 0) : d174813 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173979, d174813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173979, d174813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173980 q = 0) : d174814 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173980, d174814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173980, d174814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d173981 q = 0) : d174815 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173981, d174815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173981, d174815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173982 q = 0) : d174816 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173982, d174816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173982, d174816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15837 (p : Pattern) (selected : d173988 p = 0) : d174822 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173972 q = 0) : d174810 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173972, d174810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173972, d174810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15834 q selected
  have h2 (q : Pattern) (selected : d173983 q = 0) : d174817 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173983, d174817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173983, d174817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15836 q selected
  have h3 (q : Pattern) (selected : d173984 q = 0) : d174818 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173984, d174818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173984, d174818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173985 q = 0) : d174819 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173985, d174819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173985, d174819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173986 q = 0) : d174820 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173986, d174820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173986, d174820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173987 q = 0) : d174821 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173987, d174821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173987, d174821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d173988 q = 0) : d174822 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173988, d174822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173988, d174822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15838 (p : Pattern) (selected : d173994 p = 0) : d174828 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d173989 q = 0) : d174823 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173989, d174823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173989, d174823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15837 q selected
  have h2 (q : Pattern) (selected : d173990 q = 0) : d174824 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173990, d174824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173990, d174824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173991 q = 0) : d174825 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173991, d174825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173991, d174825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173992 q = 0) : d174826 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173992, d174826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173992, d174826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d173993 q = 0) : d174827 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173993, d174827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173993, d174827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173994 q = 0) : d174828 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173994, d174828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173994, d174828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15839 (p : Pattern) (selected : d174001 p = 0) : d174835 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d834 q = 0) : d52511 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro335 q selected
    | true =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173996 q = 0) : d174830 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173996, d174830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173996, d174830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9587 q = 0) : d101167 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, d101167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6641 q selected
    | true =>
      simp only [d9587, d101167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173997 q = 0) : d174831 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173997, d174831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173997, d174831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173998 q = 0) : d174832 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d173998, d174832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173998, d174832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9597 q = 0) : d101177 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6642 q selected
    | true =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d173999 q = 0) : d174833 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173999, d174833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173999, d174833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9468 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d173901 q = 0) : d174761 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173901, d174761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d173901, d174761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d174000 q = 0) : d174834 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174000, d174834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174000, d174834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174001 q = 0) : d174835 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174001, d174835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174001, d174835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15840 (p : Pattern) (selected : d174004 p = 0) : d174838 p = 1 := by
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
  have h2 (q : Pattern) (selected : d173898 q = 0) : d174758 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173898, d174758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173898, d174758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9458 q = 0) : d101073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6619 q selected
    | true =>
      simp only [d9458, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173899 q = 0) : d174759 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173899, d174759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173899, d174759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173900 q = 0) : d174760 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d173900, d174760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173900, d174760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9468 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d173901 q = 0) : d174761 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173901, d174761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173901, d174761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
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
  have h9 (q : Pattern) (selected : d174002 q = 0) : d174836 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174002, d174836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d174002, d174836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d174003 q = 0) : d174837 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174003, d174837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174003, d174837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174004 q = 0) : d174838 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174004, d174838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174004, d174838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15841 (p : Pattern) (selected : d174009 p = 0) : d174843 p = 1 := by
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
  have h2 (q : Pattern) (selected : d173901 q = 0) : d174761 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173901, d174761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173901, d174761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174002 q = 0) : d174836 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174002, d174836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174002, d174836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174003 q = 0) : d174837 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174003, d174837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174003, d174837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174008 q = 0) : d174842 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174008, d174842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174008, d174842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174009 q = 0) : d174843 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174009, d174843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174009, d174843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15842 (p : Pattern) (selected : d174015 p = 0) : d174849 p = 1 := by
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
  have h2 (q : Pattern) (selected : d173835 q = 0) : d174711 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173835, d174711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173835, d174711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174002 q = 0) : d174836 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174002, d174836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174002, d174836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174014 q = 0) : d174848 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174014, d174848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174014, d174848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174008 q = 0) : d174842 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174008, d174842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174008, d174842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174015 q = 0) : d174849 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174015, d174849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174015, d174849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15843 (p : Pattern) (selected : d174019 p = 0) : d174853 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174002 q = 0) : d174836 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174002, d174836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174002, d174836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174008 q = 0) : d174842 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174008, d174842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174008, d174842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174019 q = 0) : d174853 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174019, d174853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174019, d174853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro15844 (p : Pattern) (selected : d174025 p = 0) : d174859 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174005 q = 0) : d174839 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174005, d174839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15839 q selected
    | true =>
      simp only [d174005, d174839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15840 q selected
  have h2 (q : Pattern) (selected : d174006 q = 0) : d174840 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174006, d174840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174006, d174840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174007 q = 0) : d174841 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174007, d174841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174007, d174841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174010 q = 0) : d174844 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174010, d174844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15840 q selected
    | true =>
      simp only [d174010, d174844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15841 q selected
  have h5 (q : Pattern) (selected : d174011 q = 0) : d174845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174011, d174845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174011, d174845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174012 q = 0) : d174846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174012, d174846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174012, d174846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174013 q = 0) : d174847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174013, d174847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174013, d174847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174016 q = 0) : d174850 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174016, d174850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15840 q selected
    | true =>
      simp only [d174016, d174850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15842 q selected
  have h9 (q : Pattern) (selected : d174017 q = 0) : d174851 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174017, d174851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174017, d174851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174018 q = 0) : d174852 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174018, d174852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174018, d174852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174020 q = 0) : d174854 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174020, d174854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15842 q selected
    | true =>
      simp only [d174020, d174854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15843 q selected
  have h12 (q : Pattern) (selected : d174021 q = 0) : d174855 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174021, d174855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174021, d174855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d174022 q = 0) : d174856 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174022, d174856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174022, d174856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d174023 q = 0) : d174857 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174023, d174857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174023, d174857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d174024 q = 0) : d174858 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174024, d174858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174024, d174858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d174025 q = 0) : d174859 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174025, d174859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d174025, d174859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro15845 (p : Pattern) (selected : d174030 p = 0) : d174864 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174016 q = 0) : d174850 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174016, d174850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15840 q selected
    | true =>
      simp only [d174016, d174850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15842 q selected
  have h2 (q : Pattern) (selected : d174017 q = 0) : d174851 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174017, d174851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174017, d174851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174018 q = 0) : d174852 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174018, d174852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174018, d174852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174020 q = 0) : d174854 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174020, d174854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15842 q selected
    | true =>
      simp only [d174020, d174854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15843 q selected
  have h5 (q : Pattern) (selected : d174021 q = 0) : d174855 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174021, d174855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174021, d174855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174022 q = 0) : d174856 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174022, d174856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174022, d174856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174023 q = 0) : d174857 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174023, d174857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174023, d174857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174028 q = 0) : d174862 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174028, d174862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174028, d174862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174029 q = 0) : d174863 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174029, d174863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174029, d174863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174030 q = 0) : d174864 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174030, d174864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d174030, d174864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15846 (p : Pattern) (selected : d174036 p = 0) : d174870 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174026 q = 0) : d174860 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174026, d174860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15844 q selected
    | true =>
      simp only [d174026, d174860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174027 q = 0) : d174861 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174027, d174861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174027, d174861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174031 q = 0) : d174865 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174031, d174865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15845 q selected
    | true =>
      simp only [d174031, d174865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174032 q = 0) : d174866 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174032, d174866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174032, d174866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174033 q = 0) : d174867 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174033, d174867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174033, d174867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174034 q = 0) : d174868 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174034, d174868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174034, d174868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174035 q = 0) : d174869 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174035, d174869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174035, d174869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174036 q = 0) : d174870 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174036, d174870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174036, d174870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15847 (p : Pattern) (selected : d174038 p = 0) : d174872 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174020 q = 0) : d174854 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174020, d174854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15842 q selected
    | true =>
      simp only [d174020, d174854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15843 q selected
  have h2 (q : Pattern) (selected : d174021 q = 0) : d174855 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174021, d174855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174021, d174855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174022 q = 0) : d174856 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174022, d174856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174022, d174856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174028 q = 0) : d174862 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174028, d174862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174028, d174862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174037 q = 0) : d174871 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174037, d174871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174037, d174871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174038 q = 0) : d174872 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174038, d174872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174038, d174872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15848 (p : Pattern) (selected : d174044 p = 0) : d174878 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174031 q = 0) : d174865 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174031, d174865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15845 q selected
    | true =>
      simp only [d174031, d174865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174032 q = 0) : d174866 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174032, d174866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174032, d174866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174039 q = 0) : d174873 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174039, d174873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15847 q selected
    | true =>
      simp only [d174039, d174873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174040 q = 0) : d174874 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174040, d174874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174040, d174874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174041 q = 0) : d174875 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174041, d174875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174041, d174875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174042 q = 0) : d174876 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174042, d174876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174042, d174876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174043 q = 0) : d174877 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174043, d174877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174043, d174877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174044 q = 0) : d174878 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174044, d174878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174044, d174878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15849 (p : Pattern) (selected : d174052 p = 0) : d174838 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d868 q = 0) : d52290 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d868, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro341 q selected
    | true =>
      simp only [d868, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174046 q = 0) : d174758 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174046, d174758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174046, d174758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9661 q = 0) : d101073 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9661, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6654 q selected
    | true =>
      simp only [d9661, d101073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174047 q = 0) : d174759 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174047, d174759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174047, d174759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174048 q = 0) : d174760 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174048, d174760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174048, d174760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9671 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9671, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6655 q selected
    | true =>
      simp only [d9671, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174049 q = 0) : d174761 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174049, d174761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174049, d174761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d874 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174050 q = 0) : d174836 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174050, d174836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d174050, d174836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d174051 q = 0) : d174837 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174051, d174837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174051, d174837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174052 q = 0) : d174838 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174052, d174838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174052, d174838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15850 (p : Pattern) (selected : d174055 p = 0) : d174849 p = 1 := by
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
  have h2 (q : Pattern) (selected : d173934 q = 0) : d174711 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173934, d174711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173934, d174711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d874 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174050 q = 0) : d174836 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174050, d174836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174050, d174836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174053 q = 0) : d174848 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174053, d174848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174053, d174848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174054 q = 0) : d174842 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174054, d174842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174054, d174842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174055 q = 0) : d174849 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174055, d174849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174055, d174849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15851 (p : Pattern) (selected : d174059 p = 0) : d174853 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174050 q = 0) : d174836 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174050, d174836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174050, d174836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174054 q = 0) : d174842 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174054, d174842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174054, d174842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174059 q = 0) : d174853 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174059, d174853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174059, d174853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro15852 (p : Pattern) (selected : d174066 p = 0) : d174864 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174056 q = 0) : d174850 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174056, d174850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15849 q selected
    | true =>
      simp only [d174056, d174850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15850 q selected
  have h2 (q : Pattern) (selected : d174057 q = 0) : d174851 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174057, d174851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174057, d174851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174058 q = 0) : d174852 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174058, d174852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174058, d174852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174060 q = 0) : d174854 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174060, d174854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15850 q selected
    | true =>
      simp only [d174060, d174854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15851 q selected
  have h5 (q : Pattern) (selected : d174061 q = 0) : d174855 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174061, d174855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174061, d174855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174062 q = 0) : d174856 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174062, d174856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174062, d174856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174063 q = 0) : d174857 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174063, d174857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174063, d174857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174064 q = 0) : d174862 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174064, d174862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174064, d174862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174065 q = 0) : d174863 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174065, d174863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174065, d174863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174066 q = 0) : d174864 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174066, d174864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d174066, d174864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15853 (p : Pattern) (selected : d174070 p = 0) : d174872 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174060 q = 0) : d174854 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174060, d174854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15850 q selected
    | true =>
      simp only [d174060, d174854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15851 q selected
  have h2 (q : Pattern) (selected : d174061 q = 0) : d174855 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174061, d174855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174061, d174855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174062 q = 0) : d174856 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174062, d174856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174062, d174856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174064 q = 0) : d174862 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174064, d174862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174064, d174862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174069 q = 0) : d174871 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174069, d174871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174069, d174871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174070 q = 0) : d174872 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174070, d174872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174070, d174872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15854 (p : Pattern) (selected : d174076 p = 0) : d174878 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174067 q = 0) : d174865 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174067, d174865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15852 q selected
    | true =>
      simp only [d174067, d174865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174068 q = 0) : d174866 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174068, d174866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174068, d174866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174071 q = 0) : d174873 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174071, d174873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15853 q selected
    | true =>
      simp only [d174071, d174873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174072 q = 0) : d174874 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174072, d174874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174072, d174874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174073 q = 0) : d174875 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174073, d174875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174073, d174875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174074 q = 0) : d174876 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174074, d174876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174074, d174876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174075 q = 0) : d174877 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174075, d174877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174075, d174877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174076 q = 0) : d174878 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174076, d174878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174076, d174878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15855 (p : Pattern) (selected : d174080 p = 0) : d174883 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174071 q = 0) : d174873 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174071, d174873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15853 q selected
    | true =>
      simp only [d174071, d174873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174072 q = 0) : d174874 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174072, d174874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174072, d174874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174077 q = 0) : d174880 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174077, d174880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174077, d174880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174078 q = 0) : d174881 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174078, d174881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174078, d174881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174079 q = 0) : d174882 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174079, d174882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174079, d174882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174080 q = 0) : d174883 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174080, d174883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174080, d174883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15856 (p : Pattern) (selected : d174086 p = 0) : d174889 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174031 q = 0) : d174865 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174031, d174865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15845 q selected
    | true =>
      simp only [d174031, d174865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174032 q = 0) : d174866 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174032, d174866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174032, d174866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174083 q = 0) : d174886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174083, d174886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174083, d174886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174084 q = 0) : d174887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174084, d174887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174084, d174887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174085 q = 0) : d174888 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174085, d174888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174085, d174888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174086 q = 0) : d174889 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174086, d174889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174086, d174889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15857 (p : Pattern) (selected : d174092 p = 0) : d174895 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174045 q = 0) : d174879 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d174045, d174879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15846 q selected
    | true =>
      simp only [d174045, d174879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15848 q selected
  have h2 (q : Pattern) (selected : d174081 q = 0) : d174884 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d174081, d174884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15854 q selected
    | true =>
      simp only [d174081, d174884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15855 q selected
  have h3 (q : Pattern) (selected : d174082 q = 0) : d174885 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d174082, d174885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174082, d174885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174087 q = 0) : d174890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d174087, d174890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15856 q selected
    | true =>
      simp only [d174087, d174890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174088 q = 0) : d174891 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d174088, d174891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174088, d174891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174089 q = 0) : d174892 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d174089, d174892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174089, d174892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174090 q = 0) : d174893 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d174090, d174893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174090, d174893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174091 q = 0) : d174894 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d174091, d174894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174091, d174894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d174092 q = 0) : d174895 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d174092, d174895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174092, d174895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15858 (p : Pattern) (selected : d174097 p = 0) : d174883 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174039 q = 0) : d174873 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174039, d174873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15847 q selected
    | true =>
      simp only [d174039, d174873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174040 q = 0) : d174874 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174040, d174874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174040, d174874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174094 q = 0) : d174880 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174094, d174880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174094, d174880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174095 q = 0) : d174881 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174095, d174881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174095, d174881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174096 q = 0) : d174882 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174096, d174882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174096, d174882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174097 q = 0) : d174883 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174097, d174883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174097, d174883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15859 (p : Pattern) (selected : d174103 p = 0) : d174902 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174098 q = 0) : d174897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d174098, d174897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15858 q selected
    | true =>
      simp only [d174098, d174897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174099 q = 0) : d174898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d174099, d174898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174099, d174898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174100 q = 0) : d174899 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d174100, d174899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174100, d174899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174101 q = 0) : d174900 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d174101, d174900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174101, d174900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174102 q = 0) : d174901 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d174102, d174901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174102, d174901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174103 q = 0) : d174902 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d174103, d174902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174103, d174902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15860 (p : Pattern) (selected : d174109 p = 0) : d174908 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174093 q = 0) : d174896 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d174093, d174896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174093, d174896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15857 q selected
  have h2 (q : Pattern) (selected : d174104 q = 0) : d174903 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d174104, d174903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174104, d174903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15859 q selected
  have h3 (q : Pattern) (selected : d174105 q = 0) : d174904 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d174105, d174904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174105, d174904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174106 q = 0) : d174905 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d174106, d174905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174106, d174905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174107 q = 0) : d174906 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d174107, d174906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174107, d174906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174108 q = 0) : d174907 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d174108, d174907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174108, d174907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174109 q = 0) : d174908 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d174109, d174908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174109, d174908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15861 (p : Pattern) (selected : d174115 p = 0) : d174914 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174110 q = 0) : d174909 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d174110, d174909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174110, d174909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15860 q selected
  have h2 (q : Pattern) (selected : d174111 q = 0) : d174910 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d174111, d174910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174111, d174910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174112 q = 0) : d174911 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d174112, d174911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174112, d174911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174113 q = 0) : d174912 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d174113, d174912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174113, d174912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174114 q = 0) : d174913 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d174114, d174913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174114, d174913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174115 q = 0) : d174914 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d174115, d174914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174115, d174914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15862 (p : Pattern) (selected : d174124 p = 0) : d174923 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1210 q = 0) : d52791 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro407 q selected
    | true =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174118 q = 0) : d174917 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174118, d174917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174118, d174917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9753 q = 0) : d101274 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9753, d101274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6669 q selected
    | true =>
      simp only [d9753, d101274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174119 q = 0) : d174918 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174119, d174918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174119, d174918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174120 q = 0) : d174919 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174120, d174919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174120, d174919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9763 q = 0) : d101284 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9763, d101284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6670 q selected
    | true =>
      simp only [d9763, d101284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174121 q = 0) : d174920 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174121, d174920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174121, d174920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9778 q = 0) : d101299 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6672 q selected
    | true =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174122 q = 0) : d174921 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174122, d174921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d174122, d174921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d174123 q = 0) : d174922 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174123, d174922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174123, d174922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174124 q = 0) : d174923 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174124, d174923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174124, d174923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15863 (p : Pattern) (selected : d174130 p = 0) : d174929 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174125 q = 0) : d174924 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174125, d174924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174125, d174924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9789 q = 0) : d101310 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9789, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6674 q selected
    | true =>
      simp only [d9789, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174126 q = 0) : d174925 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174126, d174925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174126, d174925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174127 q = 0) : d174926 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174127, d174926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174127, d174926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9778 q = 0) : d101299 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6672 q selected
    | true =>
      simp only [d9778, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174122 q = 0) : d174921 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174122, d174921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174122, d174921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9800 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174128 q = 0) : d174927 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174128, d174927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d174128, d174927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d174129 q = 0) : d174928 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174129, d174928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174129, d174928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174130 q = 0) : d174929 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174130, d174929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174130, d174929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15864 (p : Pattern) (selected : d174137 p = 0) : d174936 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174134 q = 0) : d174933 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174134, d174933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174134, d174933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9800 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174128 q = 0) : d174927 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174128, d174927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174128, d174927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174135 q = 0) : d174934 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174135, d174934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174135, d174934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174136 q = 0) : d174935 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174136, d174935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174136, d174935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174137 q = 0) : d174936 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174137, d174936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174137, d174936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15865 (p : Pattern) (selected : d174145 p = 0) : d174944 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174142 q = 0) : d174941 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174142, d174941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174142, d174941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1121 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro388 q selected
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174143 q = 0) : d174942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174143, d174942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174143, d174942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174144 q = 0) : d174943 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174144, d174943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174144, d174943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9800 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6675 q selected
    | true =>
      simp only [d9800, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174128 q = 0) : d174927 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174128, d174927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174128, d174927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174136 q = 0) : d174935 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174136, d174935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174136, d174935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174145 q = 0) : d174944 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174145, d174944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174145, d174944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15866 (p : Pattern) (selected : d174153 p = 0) : d174952 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174149 q = 0) : d174948 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174149, d174948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174149, d174948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174150 q = 0) : d174949 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174150, d174949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174150, d174949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9844 q = 0) : d101365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6680 q selected
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174151 q = 0) : d174950 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174151, d174950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174151, d174950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174152 q = 0) : d174951 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174152, d174951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174152, d174951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174153 q = 0) : d174952 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174153, d174952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174153, d174952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15867 (p : Pattern) (selected : d174159 p = 0) : d174958 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174131 q = 0) : d174930 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174131, d174930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15862 q selected
    | true =>
      simp only [d174131, d174930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15863 q selected
  have h2 (q : Pattern) (selected : d174132 q = 0) : d174931 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174132, d174931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174132, d174931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174133 q = 0) : d174932 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174133, d174932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174133, d174932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174138 q = 0) : d174937 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174138, d174937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15863 q selected
    | true =>
      simp only [d174138, d174937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15864 q selected
  have h5 (q : Pattern) (selected : d174139 q = 0) : d174938 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174139, d174938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174139, d174938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174140 q = 0) : d174939 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174140, d174939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174140, d174939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174141 q = 0) : d174940 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174141, d174940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174141, d174940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174146 q = 0) : d174945 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174146, d174945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15863 q selected
    | true =>
      simp only [d174146, d174945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15865 q selected
  have h9 (q : Pattern) (selected : d174147 q = 0) : d174946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174147, d174946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174147, d174946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174148 q = 0) : d174947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174148, d174947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174148, d174947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174154 q = 0) : d174953 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174154, d174953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15865 q selected
    | true =>
      simp only [d174154, d174953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15866 q selected
  have h12 (q : Pattern) (selected : d174155 q = 0) : d174954 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174155, d174954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174155, d174954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d174156 q = 0) : d174955 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174156, d174955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174156, d174955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d174157 q = 0) : d174956 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174157, d174956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174157, d174956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d174158 q = 0) : d174957 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174158, d174957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174158, d174957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d174159 q = 0) : d174958 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174159, d174958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d174159, d174958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro15868 (p : Pattern) (selected : d174164 p = 0) : d174963 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174146 q = 0) : d174945 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174146, d174945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15863 q selected
    | true =>
      simp only [d174146, d174945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15865 q selected
  have h2 (q : Pattern) (selected : d174147 q = 0) : d174946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174147, d174946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174147, d174946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174148 q = 0) : d174947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174148, d174947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174148, d174947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174154 q = 0) : d174953 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174154, d174953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15865 q selected
    | true =>
      simp only [d174154, d174953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15866 q selected
  have h5 (q : Pattern) (selected : d174155 q = 0) : d174954 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174155, d174954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174155, d174954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174156 q = 0) : d174955 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174156, d174955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174156, d174955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174157 q = 0) : d174956 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174157, d174956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174157, d174956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174162 q = 0) : d174961 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174162, d174961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174162, d174961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174163 q = 0) : d174962 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174163, d174962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174163, d174962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174164 q = 0) : d174963 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174164, d174963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d174164, d174963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15869 (p : Pattern) (selected : d174170 p = 0) : d174969 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174160 q = 0) : d174959 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174160, d174959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15867 q selected
    | true =>
      simp only [d174160, d174959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174161 q = 0) : d174960 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174161, d174960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174161, d174960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174165 q = 0) : d174964 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174165, d174964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15868 q selected
    | true =>
      simp only [d174165, d174964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174166 q = 0) : d174965 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174166, d174965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174166, d174965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174167 q = 0) : d174966 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174167, d174966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174167, d174966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174168 q = 0) : d174967 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174168, d174967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174168, d174967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174169 q = 0) : d174968 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174169, d174968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174169, d174968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174170 q = 0) : d174969 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174170, d174969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174170, d174969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15870 (p : Pattern) (selected : d174172 p = 0) : d174971 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174143 q = 0) : d174942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174143, d174942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174143, d174942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174171 q = 0) : d174970 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174171, d174970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174171, d174970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9844 q = 0) : d101365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6680 q selected
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174151 q = 0) : d174950 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174151, d174950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174151, d174950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174152 q = 0) : d174951 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174152, d174951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174152, d174951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174172 q = 0) : d174971 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174172, d174971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174172, d174971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15871 (p : Pattern) (selected : d174178 p = 0) : d174977 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174173 q = 0) : d174972 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174173, d174972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15865 q selected
    | true =>
      simp only [d174173, d174972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15870 q selected
  have h2 (q : Pattern) (selected : d174174 q = 0) : d174973 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174174, d174973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174174, d174973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174175 q = 0) : d174974 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174175, d174974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174175, d174974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174176 q = 0) : d174975 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174176, d174975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174176, d174975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174177 q = 0) : d174976 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174177, d174976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174177, d174976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174178 q = 0) : d174977 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174178, d174977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174178, d174977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15872 (p : Pattern) (selected : d174184 p = 0) : d174983 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174165 q = 0) : d174964 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174165, d174964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15868 q selected
    | true =>
      simp only [d174165, d174964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174166 q = 0) : d174965 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174166, d174965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174166, d174965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174179 q = 0) : d174978 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174179, d174978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15871 q selected
    | true =>
      simp only [d174179, d174978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174180 q = 0) : d174979 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174180, d174979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174180, d174979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174181 q = 0) : d174980 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174181, d174980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174181, d174980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174182 q = 0) : d174981 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174182, d174981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174182, d174981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174183 q = 0) : d174982 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174183, d174982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174183, d174982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174184 q = 0) : d174983 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174184, d174983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174184, d174983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15873 (p : Pattern) (selected : d174192 p = 0) : d174929 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1255 q = 0) : d52681 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1255, d52681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro415 q selected
    | true =>
      simp only [d1255, d52681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174186 q = 0) : d174924 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174186, d174924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174186, d174924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9896 q = 0) : d101310 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9896, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6690 q selected
    | true =>
      simp only [d9896, d101310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174187 q = 0) : d174925 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174187, d174925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174187, d174925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174188 q = 0) : d174926 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174188, d174926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174188, d174926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9908 q = 0) : d101299 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9908, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6691 q selected
    | true =>
      simp only [d9908, d101299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174189 q = 0) : d174921 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174189, d174921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174189, d174921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9918 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6692 q selected
    | true =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174190 q = 0) : d174927 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174190, d174927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d174190, d174927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d174191 q = 0) : d174928 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174191, d174928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174191, d174928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174192 q = 0) : d174929 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174192, d174929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174192, d174929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15874 (p : Pattern) (selected : d174197 p = 0) : d174944 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174193 q = 0) : d174941 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174193, d174941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174193, d174941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1276 q = 0) : d52702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro417 q selected
    | true =>
      simp only [d1276, d52702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174194 q = 0) : d174942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174194, d174942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174194, d174942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174195 q = 0) : d174943 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174195, d174943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174195, d174943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9918 q = 0) : d101321 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6692 q selected
    | true =>
      simp only [d9918, d101321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174190 q = 0) : d174927 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174190, d174927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174190, d174927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174196 q = 0) : d174935 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174196, d174935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174196, d174935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174197 q = 0) : d174944 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174197, d174944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174197, d174944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15875 (p : Pattern) (selected : d174205 p = 0) : d174952 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174201 q = 0) : d174948 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174201, d174948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174201, d174948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174202 q = 0) : d174949 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174202, d174949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174202, d174949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9952 q = 0) : d101365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6696 q selected
    | true =>
      simp only [d9952, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174203 q = 0) : d174950 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174203, d174950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174203, d174950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174204 q = 0) : d174951 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174204, d174951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174204, d174951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174205 q = 0) : d174952 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174205, d174952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174205, d174952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15876 (p : Pattern) (selected : d174211 p = 0) : d174971 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174194 q = 0) : d174942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174194, d174942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174194, d174942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174210 q = 0) : d174970 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174210, d174970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174210, d174970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9952 q = 0) : d101365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6696 q selected
    | true =>
      simp only [d9952, d101365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174203 q = 0) : d174950 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174203, d174950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174203, d174950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174204 q = 0) : d174951 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174204, d174951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174204, d174951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174211 q = 0) : d174971 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174211, d174971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174211, d174971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15877 (p : Pattern) (selected : d174217 p = 0) : d174986 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174198 q = 0) : d174945 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174198, d174945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15873 q selected
    | true =>
      simp only [d174198, d174945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15874 q selected
  have h2 (q : Pattern) (selected : d174199 q = 0) : d174946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174199, d174946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174199, d174946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174200 q = 0) : d174947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174200, d174947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174200, d174947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174206 q = 0) : d174953 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174206, d174953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15874 q selected
    | true =>
      simp only [d174206, d174953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15875 q selected
  have h5 (q : Pattern) (selected : d174207 q = 0) : d174954 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174207, d174954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174207, d174954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174208 q = 0) : d174955 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174208, d174955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174208, d174955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174209 q = 0) : d174956 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174209, d174956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174209, d174956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174212 q = 0) : d174972 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174212, d174972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15874 q selected
    | true =>
      simp only [d174212, d174972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15876 q selected
  have h9 (q : Pattern) (selected : d174213 q = 0) : d174973 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174213, d174973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174213, d174973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174214 q = 0) : d174974 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174214, d174974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174214, d174974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174215 q = 0) : d174975 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174215, d174975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174215, d174975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d174216 q = 0) : d174985 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174216, d174985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174216, d174985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d174217 q = 0) : d174986 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174217, d174986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d174217, d174986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro15878 (p : Pattern) (selected : d174221 p = 0) : d174977 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174212 q = 0) : d174972 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174212, d174972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15874 q selected
    | true =>
      simp only [d174212, d174972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15876 q selected
  have h2 (q : Pattern) (selected : d174213 q = 0) : d174973 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174213, d174973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174213, d174973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174214 q = 0) : d174974 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174214, d174974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174214, d174974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174215 q = 0) : d174975 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174215, d174975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174215, d174975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174220 q = 0) : d174976 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174220, d174976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174220, d174976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174221 q = 0) : d174977 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174221, d174977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174221, d174977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15879 (p : Pattern) (selected : d174227 p = 0) : d174992 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174218 q = 0) : d174987 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174218, d174987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15877 q selected
    | true =>
      simp only [d174218, d174987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174219 q = 0) : d174988 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174219, d174988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174219, d174988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174222 q = 0) : d174978 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174222, d174978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15878 q selected
    | true =>
      simp only [d174222, d174978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174223 q = 0) : d174979 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174223, d174979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174223, d174979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174224 q = 0) : d174989 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174224, d174989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174224, d174989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174225 q = 0) : d174990 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174225, d174990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174225, d174990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174226 q = 0) : d174991 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174226, d174991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174226, d174991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174227 q = 0) : d174992 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174227, d174992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174227, d174992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15880 (p : Pattern) (selected : d174231 p = 0) : d174996 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174222 q = 0) : d174978 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174222, d174978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15878 q selected
    | true =>
      simp only [d174222, d174978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174223 q = 0) : d174979 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174223, d174979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174223, d174979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174228 q = 0) : d174993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174228, d174993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174228, d174993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174229 q = 0) : d174994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174229, d174994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174229, d174994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174230 q = 0) : d174995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174230, d174995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174230, d174995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174231 q = 0) : d174996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174231, d174996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174231, d174996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15881 (p : Pattern) (selected : d174234 p = 0) : d174999 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174143 q = 0) : d174942 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174143, d174942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174143, d174942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174171 q = 0) : d174970 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174171, d174970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174171, d174970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174234 q = 0) : d174999 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174234, d174999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174234, d174999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro15882 (p : Pattern) (selected : d174240 p = 0) : d175005 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174146 q = 0) : d174945 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174146, d174945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15863 q selected
    | true =>
      simp only [d174146, d174945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15865 q selected
  have h2 (q : Pattern) (selected : d174147 q = 0) : d174946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174147, d174946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174147, d174946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174148 q = 0) : d174947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174148, d174947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174148, d174947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174154 q = 0) : d174953 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174154, d174953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15865 q selected
    | true =>
      simp only [d174154, d174953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15866 q selected
  have h5 (q : Pattern) (selected : d174155 q = 0) : d174954 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174155, d174954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174155, d174954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174156 q = 0) : d174955 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174156, d174955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174156, d174955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174157 q = 0) : d174956 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174157, d174956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174157, d174956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174235 q = 0) : d175000 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174235, d175000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15865 q selected
    | true =>
      simp only [d174235, d175000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15881 q selected
  have h9 (q : Pattern) (selected : d174236 q = 0) : d175001 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174236, d175001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174236, d175001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174237 q = 0) : d175002 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174237, d175002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174237, d175002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174238 q = 0) : d175003 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174238, d175003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174238, d175003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d174239 q = 0) : d175004 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174239, d175004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174239, d175004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d174240 q = 0) : d175005 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174240, d175005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d174240, d175005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro15883 (p : Pattern) (selected : d174246 p = 0) : d175011 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174241 q = 0) : d175006 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174241, d175006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15882 q selected
    | true =>
      simp only [d174241, d175006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174242 q = 0) : d175007 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174242, d175007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174242, d175007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174243 q = 0) : d175008 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174243, d175008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174243, d175008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174244 q = 0) : d175009 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174244, d175009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174244, d175009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174245 q = 0) : d175010 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174245, d175010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174245, d175010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174246 q = 0) : d175011 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174246, d175011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174246, d175011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15884 (p : Pattern) (selected : d174252 p = 0) : d175017 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174185 q = 0) : d174984 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d174185, d174984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15869 q selected
    | true =>
      simp only [d174185, d174984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15872 q selected
  have h2 (q : Pattern) (selected : d174232 q = 0) : d174997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d174232, d174997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15879 q selected
    | true =>
      simp only [d174232, d174997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15880 q selected
  have h3 (q : Pattern) (selected : d174233 q = 0) : d174998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d174233, d174998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174233, d174998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174247 q = 0) : d175012 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d174247, d175012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15883 q selected
    | true =>
      simp only [d174247, d175012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174248 q = 0) : d175013 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d174248, d175013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174248, d175013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174249 q = 0) : d175014 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d174249, d175014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174249, d175014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174250 q = 0) : d175015 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d174250, d175015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174250, d175015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174251 q = 0) : d175016 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d174251, d175016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174251, d175016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d174252 q = 0) : d175017 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d174252, d175017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174252, d175017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15885 (p : Pattern) (selected : d174257 p = 0) : d174996 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174179 q = 0) : d174978 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174179, d174978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15871 q selected
    | true =>
      simp only [d174179, d174978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174180 q = 0) : d174979 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174180, d174979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174180, d174979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174254 q = 0) : d174993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174254, d174993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174254, d174993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174255 q = 0) : d174994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174255, d174994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174255, d174994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174256 q = 0) : d174995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174256, d174995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174256, d174995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174257 q = 0) : d174996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174257, d174996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174257, d174996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15886 (p : Pattern) (selected : d174263 p = 0) : d175024 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174258 q = 0) : d175019 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d174258, d175019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15885 q selected
    | true =>
      simp only [d174258, d175019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174259 q = 0) : d175020 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d174259, d175020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174259, d175020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174260 q = 0) : d175021 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d174260, d175021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174260, d175021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174261 q = 0) : d175022 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d174261, d175022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174261, d175022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174262 q = 0) : d175023 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d174262, d175023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174262, d175023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174263 q = 0) : d175024 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d174263, d175024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174263, d175024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15887 (p : Pattern) (selected : d174269 p = 0) : d175030 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174253 q = 0) : d175018 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d174253, d175018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174253, d175018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15884 q selected
  have h2 (q : Pattern) (selected : d174264 q = 0) : d175025 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d174264, d175025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174264, d175025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15886 q selected
  have h3 (q : Pattern) (selected : d174265 q = 0) : d175026 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d174265, d175026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174265, d175026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174266 q = 0) : d175027 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d174266, d175027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174266, d175027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174267 q = 0) : d175028 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d174267, d175028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174267, d175028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174268 q = 0) : d175029 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d174268, d175029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174268, d175029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174269 q = 0) : d175030 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d174269, d175030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174269, d175030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15888 (p : Pattern) (selected : d174275 p = 0) : d175036 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174270 q = 0) : d175031 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d174270, d175031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174270, d175031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15887 q selected
  have h2 (q : Pattern) (selected : d174271 q = 0) : d175032 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d174271, d175032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174271, d175032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174272 q = 0) : d175033 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d174272, d175033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174272, d175033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174273 q = 0) : d175034 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d174273, d175034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174273, d175034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174274 q = 0) : d175035 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d174274, d175035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174274, d175035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174275 q = 0) : d175036 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d174275, d175036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174275, d175036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15889 (p : Pattern) (selected : d174285 p = 0) : d175046 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1665 q = 0) : d53106 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro487 q selected
    | true =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174279 q = 0) : d175040 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174279, d175040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174279, d175040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10036 q = 0) : d101463 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6711 q selected
    | true =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174280 q = 0) : d175041 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174280, d175041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174280, d175041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174281 q = 0) : d175042 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174281, d175042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174281, d175042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10046 q = 0) : d101473 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6712 q selected
    | true =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174282 q = 0) : d175043 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174282, d175043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174282, d175043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10063 q = 0) : d101490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6714 q selected
    | true =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174283 q = 0) : d175044 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174283, d175044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d174283, d175044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d174284 q = 0) : d175045 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174284, d175045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174284, d175045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174285 q = 0) : d175046 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174285, d175046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174285, d175046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15890 (p : Pattern) (selected : d174291 p = 0) : d175052 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1555 q = 0) : d52996 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro466 q selected
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174286 q = 0) : d175047 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174286, d175047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174286, d175047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10074 q = 0) : d101501 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10074, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6716 q selected
    | true =>
      simp only [d10074, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174287 q = 0) : d175048 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174287, d175048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174287, d175048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174288 q = 0) : d175049 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174288, d175049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174288, d175049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10063 q = 0) : d101490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6714 q selected
    | true =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174283 q = 0) : d175044 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174283, d175044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174283, d175044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10085 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174289 q = 0) : d175050 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174289, d175050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d174289, d175050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d174290 q = 0) : d175051 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174290, d175051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174290, d175051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174291 q = 0) : d175052 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174291, d175052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174291, d175052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15891 (p : Pattern) (selected : d174298 p = 0) : d175059 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174295 q = 0) : d175056 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174295, d175056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174295, d175056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10085 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174289 q = 0) : d175050 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174289, d175050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174289, d175050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174296 q = 0) : d175057 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174296, d175057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174296, d175057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174297 q = 0) : d175058 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174297, d175058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174297, d175058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174298 q = 0) : d175059 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174298, d175059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174298, d175059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15892 (p : Pattern) (selected : d174306 p = 0) : d175067 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1570 q = 0) : d53011 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro469 q selected
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174303 q = 0) : d175064 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174303, d175064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174303, d175064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10115 q = 0) : d101542 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10115, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6721 q selected
    | true =>
      simp only [d10115, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174304 q = 0) : d175065 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174304, d175065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174304, d175065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174305 q = 0) : d175066 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174305, d175066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174305, d175066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10085 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174289 q = 0) : d175050 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174289, d175050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174289, d175050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174297 q = 0) : d175058 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174297, d175058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174297, d175058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174306 q = 0) : d175067 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174306, d175067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174306, d175067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15893 (p : Pattern) (selected : d174314 p = 0) : d175075 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174310 q = 0) : d175071 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174310, d175071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174310, d175071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174311 q = 0) : d175072 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174311, d175072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174311, d175072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10135 q = 0) : d101562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6723 q selected
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174312 q = 0) : d175073 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174312, d175073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174312, d175073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174313 q = 0) : d175074 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174313, d175074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174313, d175074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174314 q = 0) : d175075 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174314, d175075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174314, d175075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15894 (p : Pattern) (selected : d174320 p = 0) : d175081 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174292 q = 0) : d175053 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174292, d175053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15889 q selected
    | true =>
      simp only [d174292, d175053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15890 q selected
  have h2 (q : Pattern) (selected : d174293 q = 0) : d175054 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174293, d175054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174293, d175054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174294 q = 0) : d175055 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174294, d175055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174294, d175055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174299 q = 0) : d175060 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174299, d175060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15890 q selected
    | true =>
      simp only [d174299, d175060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15891 q selected
  have h5 (q : Pattern) (selected : d174300 q = 0) : d175061 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174300, d175061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174300, d175061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174301 q = 0) : d175062 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174301, d175062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174301, d175062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174302 q = 0) : d175063 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174302, d175063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174302, d175063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174307 q = 0) : d175068 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174307, d175068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15890 q selected
    | true =>
      simp only [d174307, d175068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15892 q selected
  have h9 (q : Pattern) (selected : d174308 q = 0) : d175069 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174308, d175069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174308, d175069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174309 q = 0) : d175070 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174309, d175070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174309, d175070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174315 q = 0) : d175076 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174315, d175076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15892 q selected
    | true =>
      simp only [d174315, d175076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15893 q selected
  have h12 (q : Pattern) (selected : d174316 q = 0) : d175077 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174316, d175077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174316, d175077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d174317 q = 0) : d175078 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174317, d175078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174317, d175078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d174318 q = 0) : d175079 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174318, d175079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174318, d175079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d174319 q = 0) : d175080 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174319, d175080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174319, d175080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d174320 q = 0) : d175081 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174320, d175081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d174320, d175081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro15895 (p : Pattern) (selected : d174325 p = 0) : d175086 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174307 q = 0) : d175068 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174307, d175068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15890 q selected
    | true =>
      simp only [d174307, d175068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15892 q selected
  have h2 (q : Pattern) (selected : d174308 q = 0) : d175069 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174308, d175069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174308, d175069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174309 q = 0) : d175070 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174309, d175070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174309, d175070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174315 q = 0) : d175076 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174315, d175076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15892 q selected
    | true =>
      simp only [d174315, d175076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15893 q selected
  have h5 (q : Pattern) (selected : d174316 q = 0) : d175077 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174316, d175077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174316, d175077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174317 q = 0) : d175078 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174317, d175078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174317, d175078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174318 q = 0) : d175079 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174318, d175079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174318, d175079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174323 q = 0) : d175084 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174323, d175084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174323, d175084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174324 q = 0) : d175085 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174324, d175085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174324, d175085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174325 q = 0) : d175086 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174325, d175086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d174325, d175086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15896 (p : Pattern) (selected : d174331 p = 0) : d175092 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174321 q = 0) : d175082 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174321, d175082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15894 q selected
    | true =>
      simp only [d174321, d175082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174322 q = 0) : d175083 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174322, d175083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174322, d175083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174326 q = 0) : d175087 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174326, d175087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15895 q selected
    | true =>
      simp only [d174326, d175087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174327 q = 0) : d175088 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174327, d175088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174327, d175088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174328 q = 0) : d175089 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174328, d175089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174328, d175089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174329 q = 0) : d175090 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174329, d175090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174329, d175090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174330 q = 0) : d175091 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174330, d175091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174330, d175091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174331 q = 0) : d175092 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174331, d175092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174331, d175092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15897 (p : Pattern) (selected : d174334 p = 0) : d175095 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1582 q = 0) : d53023 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro470 q selected
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174332 q = 0) : d175093 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174332, d175093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174332, d175093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174333 q = 0) : d175094 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174333, d175094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174333, d175094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10135 q = 0) : d101562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6723 q selected
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174312 q = 0) : d175073 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174312, d175073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174312, d175073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174313 q = 0) : d175074 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174313, d175074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174313, d175074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174334 q = 0) : d175095 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174334, d175095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174334, d175095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15898 (p : Pattern) (selected : d174340 p = 0) : d175101 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174335 q = 0) : d175096 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174335, d175096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15892 q selected
    | true =>
      simp only [d174335, d175096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15897 q selected
  have h2 (q : Pattern) (selected : d174336 q = 0) : d175097 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174336, d175097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174336, d175097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174337 q = 0) : d175098 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174337, d175098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174337, d175098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174338 q = 0) : d175099 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174338, d175099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174338, d175099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174339 q = 0) : d175100 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174339, d175100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174339, d175100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174340 q = 0) : d175101 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174340, d175101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174340, d175101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15899 (p : Pattern) (selected : d174346 p = 0) : d175107 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174326 q = 0) : d175087 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174326, d175087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15895 q selected
    | true =>
      simp only [d174326, d175087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174327 q = 0) : d175088 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174327, d175088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174327, d175088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174341 q = 0) : d175102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174341, d175102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15898 q selected
    | true =>
      simp only [d174341, d175102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174342 q = 0) : d175103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174342, d175103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174342, d175103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174343 q = 0) : d175104 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174343, d175104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174343, d175104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174344 q = 0) : d175105 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174344, d175105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174344, d175105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174345 q = 0) : d175106 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174345, d175106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174345, d175106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174346 q = 0) : d175107 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174346, d175107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174346, d175107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15900 (p : Pattern) (selected : d174354 p = 0) : d175052 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1726 q = 0) : d52996 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1726, d52996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro499 q selected
    | true =>
      simp only [d1726, d52996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174348 q = 0) : d175047 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174348, d175047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174348, d175047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10190 q = 0) : d101501 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10190, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6733 q selected
    | true =>
      simp only [d10190, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174349 q = 0) : d175048 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174349, d175048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174349, d175048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174350 q = 0) : d175049 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174350, d175049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174350, d175049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10200 q = 0) : d101490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10200, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6734 q selected
    | true =>
      simp only [d10200, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174351 q = 0) : d175044 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174351, d175044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174351, d175044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10215 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6735 q selected
    | true =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174352 q = 0) : d175050 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174352, d175050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d174352, d175050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d174353 q = 0) : d175051 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174353, d175051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174353, d175051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174354 q = 0) : d175052 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174354, d175052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174354, d175052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15901 (p : Pattern) (selected : d174359 p = 0) : d175067 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1741 q = 0) : d53011 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1741, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro502 q selected
    | true =>
      simp only [d1741, d53011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174355 q = 0) : d175064 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174355, d175064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174355, d175064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10226 q = 0) : d101542 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10226, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6737 q selected
    | true =>
      simp only [d10226, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174356 q = 0) : d175065 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174356, d175065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174356, d175065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174357 q = 0) : d175066 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174357, d175066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174357, d175066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10215 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6735 q selected
    | true =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174352 q = 0) : d175050 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174352, d175050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174352, d175050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174358 q = 0) : d175058 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174358, d175058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174358, d175058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174359 q = 0) : d175067 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174359, d175067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174359, d175067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15902 (p : Pattern) (selected : d174367 p = 0) : d175075 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174363 q = 0) : d175071 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174363, d175071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174363, d175071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174364 q = 0) : d175072 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174364, d175072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174364, d175072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10255 q = 0) : d101562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6740 q selected
    | true =>
      simp only [d10255, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174365 q = 0) : d175073 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174365, d175073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174365, d175073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174366 q = 0) : d175074 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174366, d175074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174366, d175074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174367 q = 0) : d175075 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174367, d175075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174367, d175075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15903 (p : Pattern) (selected : d174374 p = 0) : d175095 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1753 q = 0) : d53023 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro503 q selected
    | true =>
      simp only [d1753, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174372 q = 0) : d175093 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174372, d175093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174372, d175093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174373 q = 0) : d175094 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174373, d175094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174373, d175094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10255 q = 0) : d101562 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6740 q selected
    | true =>
      simp only [d10255, d101562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174365 q = 0) : d175073 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174365, d175073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174365, d175073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174366 q = 0) : d175074 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174366, d175074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174366, d175074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174374 q = 0) : d175095 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174374, d175095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174374, d175095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15904 (p : Pattern) (selected : d174380 p = 0) : d175110 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174360 q = 0) : d175068 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174360, d175068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15900 q selected
    | true =>
      simp only [d174360, d175068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15901 q selected
  have h2 (q : Pattern) (selected : d174361 q = 0) : d175069 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174361, d175069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174361, d175069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174362 q = 0) : d175070 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174362, d175070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174362, d175070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174368 q = 0) : d175076 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174368, d175076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15901 q selected
    | true =>
      simp only [d174368, d175076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15902 q selected
  have h5 (q : Pattern) (selected : d174369 q = 0) : d175077 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174369, d175077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174369, d175077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174370 q = 0) : d175078 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174370, d175078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174370, d175078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174371 q = 0) : d175079 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174371, d175079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174371, d175079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174375 q = 0) : d175096 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174375, d175096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15901 q selected
    | true =>
      simp only [d174375, d175096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15903 q selected
  have h9 (q : Pattern) (selected : d174376 q = 0) : d175097 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174376, d175097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174376, d175097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174377 q = 0) : d175098 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174377, d175098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174377, d175098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174378 q = 0) : d175099 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174378, d175099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174378, d175099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d174379 q = 0) : d175109 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174379, d175109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174379, d175109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d174380 q = 0) : d175110 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174380, d175110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d174380, d175110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro15905 (p : Pattern) (selected : d174384 p = 0) : d175101 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174375 q = 0) : d175096 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174375, d175096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15901 q selected
    | true =>
      simp only [d174375, d175096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15903 q selected
  have h2 (q : Pattern) (selected : d174376 q = 0) : d175097 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174376, d175097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174376, d175097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174377 q = 0) : d175098 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174377, d175098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174377, d175098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174378 q = 0) : d175099 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174378, d175099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174378, d175099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174383 q = 0) : d175100 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174383, d175100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174383, d175100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174384 q = 0) : d175101 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174384, d175101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174384, d175101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15906 (p : Pattern) (selected : d174390 p = 0) : d175116 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174381 q = 0) : d175111 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174381, d175111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15904 q selected
    | true =>
      simp only [d174381, d175111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174382 q = 0) : d175112 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174382, d175112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174382, d175112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174385 q = 0) : d175102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174385, d175102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15905 q selected
    | true =>
      simp only [d174385, d175102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174386 q = 0) : d175103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174386, d175103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174386, d175103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174387 q = 0) : d175113 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174387, d175113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174387, d175113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174388 q = 0) : d175114 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174388, d175114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174388, d175114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174389 q = 0) : d175115 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174389, d175115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174389, d175115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174390 q = 0) : d175116 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174390, d175116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174390, d175116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15907 (p : Pattern) (selected : d174394 p = 0) : d175120 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174385 q = 0) : d175102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174385, d175102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15905 q selected
    | true =>
      simp only [d174385, d175102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174386 q = 0) : d175103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174386, d175103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174386, d175103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174391 q = 0) : d175117 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174391, d175117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174391, d175117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174392 q = 0) : d175118 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174392, d175118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174392, d175118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174393 q = 0) : d175119 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174393, d175119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174393, d175119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174394 q = 0) : d175120 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174394, d175120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174394, d175120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15908 (p : Pattern) (selected : d174397 p = 0) : d175123 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1582 q = 0) : d53023 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro470 q selected
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174332 q = 0) : d175093 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174332, d175093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174332, d175093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174333 q = 0) : d175094 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174333, d175094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174333, d175094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174397 q = 0) : d175123 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174397, d175123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174397, d175123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro15909 (p : Pattern) (selected : d174403 p = 0) : d175129 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174307 q = 0) : d175068 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174307, d175068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15890 q selected
    | true =>
      simp only [d174307, d175068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15892 q selected
  have h2 (q : Pattern) (selected : d174308 q = 0) : d175069 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174308, d175069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174308, d175069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174309 q = 0) : d175070 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174309, d175070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174309, d175070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174315 q = 0) : d175076 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174315, d175076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15892 q selected
    | true =>
      simp only [d174315, d175076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15893 q selected
  have h5 (q : Pattern) (selected : d174316 q = 0) : d175077 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174316, d175077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174316, d175077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174317 q = 0) : d175078 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174317, d175078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174317, d175078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174318 q = 0) : d175079 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174318, d175079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174318, d175079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174398 q = 0) : d175124 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174398, d175124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15892 q selected
    | true =>
      simp only [d174398, d175124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15908 q selected
  have h9 (q : Pattern) (selected : d174399 q = 0) : d175125 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174399, d175125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174399, d175125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174400 q = 0) : d175126 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174400, d175126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174400, d175126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174401 q = 0) : d175127 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174401, d175127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174401, d175127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d174402 q = 0) : d175128 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174402, d175128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174402, d175128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d174403 q = 0) : d175129 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174403, d175129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d174403, d175129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro15910 (p : Pattern) (selected : d174409 p = 0) : d175135 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174404 q = 0) : d175130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174404, d175130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15909 q selected
    | true =>
      simp only [d174404, d175130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174405 q = 0) : d175131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174405, d175131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174405, d175131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174406 q = 0) : d175132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174406, d175132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174406, d175132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174407 q = 0) : d175133 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174407, d175133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174407, d175133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174408 q = 0) : d175134 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174408, d175134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174408, d175134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174409 q = 0) : d175135 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174409, d175135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174409, d175135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15911 (p : Pattern) (selected : d174415 p = 0) : d175141 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174347 q = 0) : d175108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d174347, d175108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15896 q selected
    | true =>
      simp only [d174347, d175108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15899 q selected
  have h2 (q : Pattern) (selected : d174395 q = 0) : d175121 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d174395, d175121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15906 q selected
    | true =>
      simp only [d174395, d175121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15907 q selected
  have h3 (q : Pattern) (selected : d174396 q = 0) : d175122 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d174396, d175122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174396, d175122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174410 q = 0) : d175136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d174410, d175136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15910 q selected
    | true =>
      simp only [d174410, d175136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174411 q = 0) : d175137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d174411, d175137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174411, d175137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174412 q = 0) : d175138 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d174412, d175138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174412, d175138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174413 q = 0) : d175139 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d174413, d175139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174413, d175139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174414 q = 0) : d175140 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d174414, d175140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174414, d175140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d174415 q = 0) : d175141 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d174415, d175141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174415, d175141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15912 (p : Pattern) (selected : d174420 p = 0) : d175120 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174341 q = 0) : d175102 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174341, d175102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15898 q selected
    | true =>
      simp only [d174341, d175102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174342 q = 0) : d175103 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174342, d175103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174342, d175103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174417 q = 0) : d175117 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174417, d175117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174417, d175117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174418 q = 0) : d175118 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174418, d175118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174418, d175118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174419 q = 0) : d175119 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174419, d175119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174419, d175119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174420 q = 0) : d175120 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174420, d175120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174420, d175120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15913 (p : Pattern) (selected : d174426 p = 0) : d175148 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174421 q = 0) : d175143 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d174421, d175143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15912 q selected
    | true =>
      simp only [d174421, d175143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174422 q = 0) : d175144 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d174422, d175144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174422, d175144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174423 q = 0) : d175145 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d174423, d175145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174423, d175145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174424 q = 0) : d175146 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d174424, d175146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174424, d175146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174425 q = 0) : d175147 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d174425, d175147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174425, d175147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174426 q = 0) : d175148 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d174426, d175148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174426, d175148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15914 (p : Pattern) (selected : d174432 p = 0) : d175154 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174416 q = 0) : d175142 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d174416, d175142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174416, d175142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15911 q selected
  have h2 (q : Pattern) (selected : d174427 q = 0) : d175149 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d174427, d175149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174427, d175149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15913 q selected
  have h3 (q : Pattern) (selected : d174428 q = 0) : d175150 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d174428, d175150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174428, d175150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174429 q = 0) : d175151 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d174429, d175151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174429, d175151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174430 q = 0) : d175152 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d174430, d175152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174430, d175152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174431 q = 0) : d175153 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d174431, d175153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174431, d175153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174432 q = 0) : d175154 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d174432, d175154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174432, d175154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15915 (p : Pattern) (selected : d174438 p = 0) : d175160 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174433 q = 0) : d175155 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d174433, d175155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174433, d175155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15914 q selected
  have h2 (q : Pattern) (selected : d174434 q = 0) : d175156 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d174434, d175156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174434, d175156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174435 q = 0) : d175157 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d174435, d175157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174435, d175157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174436 q = 0) : d175158 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d174436, d175158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174436, d175158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174437 q = 0) : d175159 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d174437, d175159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174437, d175159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174438 q = 0) : d175160 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d174438, d175160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174438, d175160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15916 (p : Pattern) (selected : d174448 p = 0) : d175170 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2144 q = 0) : d53423 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro576 q selected
    | true =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174443 q = 0) : d175165 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174443, d175165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174443, d175165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10343 q = 0) : d101664 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6755 q selected
    | true =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174444 q = 0) : d175166 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174444, d175166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174444, d175166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174445 q = 0) : d175167 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174445, d175167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174445, d175167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10353 q = 0) : d101674 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174446 q = 0) : d175168 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174446, d175168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174446, d175168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174447 q = 0) : d175169 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174447, d175169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174447, d175169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d174448 q = 0) : d175170 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174448, d175170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174448, d175170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15917 (p : Pattern) (selected : d174454 p = 0) : d175176 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2035 q = 0) : d53314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro553 q selected
    | true =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174449 q = 0) : d175171 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174449, d175171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174449, d175171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10364 q = 0) : d101685 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6758 q selected
    | true =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174450 q = 0) : d175172 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174450, d175172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174450, d175172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174451 q = 0) : d175173 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174451, d175173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174451, d175173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10353 q = 0) : d101674 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174446 q = 0) : d175168 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174446, d175168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174446, d175168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10371 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174452 q = 0) : d175174 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174452, d175174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d174452, d175174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d174453 q = 0) : d175175 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174453, d175175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174453, d175175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174454 q = 0) : d175176 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174454, d175176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174454, d175176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15918 (p : Pattern) (selected : d174459 p = 0) : d175181 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174446 q = 0) : d175168 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174446, d175168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174446, d175168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10371 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174452 q = 0) : d175174 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174452, d175174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174452, d175174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174453 q = 0) : d175175 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174453, d175175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174453, d175175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174458 q = 0) : d175180 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174458, d175180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174458, d175180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174459 q = 0) : d175181 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174459, d175181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174459, d175181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15919 (p : Pattern) (selected : d174467 p = 0) : d175189 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2053 q = 0) : d53332 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro558 q selected
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174464 q = 0) : d175186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174464, d175186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174464, d175186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10391 q = 0) : d101712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10391, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6762 q selected
    | true =>
      simp only [d10391, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174465 q = 0) : d175187 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174465, d175187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174465, d175187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174466 q = 0) : d175188 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174466, d175188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174466, d175188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10371 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174452 q = 0) : d175174 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174452, d175174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174452, d175174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174458 q = 0) : d175180 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174458, d175180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174458, d175180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174467 q = 0) : d175189 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174467, d175189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174467, d175189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15920 (p : Pattern) (selected : d174475 p = 0) : d175197 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174471 q = 0) : d175193 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174471, d175193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174471, d175193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174472 q = 0) : d175194 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174472, d175194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174472, d175194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10412 q = 0) : d101733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6764 q selected
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174473 q = 0) : d175195 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174473, d175195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174473, d175195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174474 q = 0) : d175196 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174474, d175196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174474, d175196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174475 q = 0) : d175197 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174475, d175197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174475, d175197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15921 (p : Pattern) (selected : d174481 p = 0) : d175203 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174455 q = 0) : d175177 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174455, d175177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15916 q selected
    | true =>
      simp only [d174455, d175177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15917 q selected
  have h2 (q : Pattern) (selected : d174456 q = 0) : d175178 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174456, d175178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174456, d175178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174457 q = 0) : d175179 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174457, d175179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174457, d175179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174460 q = 0) : d175182 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174460, d175182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15917 q selected
    | true =>
      simp only [d174460, d175182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15918 q selected
  have h5 (q : Pattern) (selected : d174461 q = 0) : d175183 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174461, d175183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174461, d175183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174462 q = 0) : d175184 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174462, d175184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174462, d175184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174463 q = 0) : d175185 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174463, d175185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174463, d175185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174468 q = 0) : d175190 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174468, d175190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15917 q selected
    | true =>
      simp only [d174468, d175190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15919 q selected
  have h9 (q : Pattern) (selected : d174469 q = 0) : d175191 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174469, d175191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174469, d175191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174470 q = 0) : d175192 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174470, d175192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174470, d175192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174476 q = 0) : d175198 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174476, d175198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15919 q selected
    | true =>
      simp only [d174476, d175198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15920 q selected
  have h12 (q : Pattern) (selected : d174477 q = 0) : d175199 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174477, d175199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174477, d175199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d174478 q = 0) : d175200 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174478, d175200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174478, d175200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d174479 q = 0) : d175201 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174479, d175201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174479, d175201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d174480 q = 0) : d175202 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174480, d175202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174480, d175202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d174481 q = 0) : d175203 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174481, d175203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d174481, d175203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro15922 (p : Pattern) (selected : d174486 p = 0) : d175208 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174468 q = 0) : d175190 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174468, d175190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15917 q selected
    | true =>
      simp only [d174468, d175190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15919 q selected
  have h2 (q : Pattern) (selected : d174469 q = 0) : d175191 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174469, d175191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174469, d175191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174470 q = 0) : d175192 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174470, d175192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174470, d175192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174476 q = 0) : d175198 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174476, d175198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15919 q selected
    | true =>
      simp only [d174476, d175198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15920 q selected
  have h5 (q : Pattern) (selected : d174477 q = 0) : d175199 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174477, d175199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174477, d175199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174478 q = 0) : d175200 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174478, d175200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174478, d175200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174479 q = 0) : d175201 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174479, d175201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174479, d175201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174484 q = 0) : d175206 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174484, d175206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174484, d175206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174485 q = 0) : d175207 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174485, d175207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174485, d175207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174486 q = 0) : d175208 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174486, d175208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d174486, d175208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15923 (p : Pattern) (selected : d174492 p = 0) : d175214 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174482 q = 0) : d175204 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174482, d175204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15921 q selected
    | true =>
      simp only [d174482, d175204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174483 q = 0) : d175205 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174483, d175205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174483, d175205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174487 q = 0) : d175209 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174487, d175209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15922 q selected
    | true =>
      simp only [d174487, d175209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174488 q = 0) : d175210 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174488, d175210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174488, d175210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174489 q = 0) : d175211 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174489, d175211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174489, d175211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174490 q = 0) : d175212 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174490, d175212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174490, d175212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174491 q = 0) : d175213 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174491, d175213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174491, d175213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174492 q = 0) : d175214 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174492, d175214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174492, d175214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15924 (p : Pattern) (selected : d174495 p = 0) : d175217 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2065 q = 0) : d53344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174493 q = 0) : d175215 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174493, d175215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174493, d175215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174494 q = 0) : d175216 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174494, d175216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174494, d175216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10412 q = 0) : d101733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6764 q selected
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174473 q = 0) : d175195 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174473, d175195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174473, d175195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174474 q = 0) : d175196 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174474, d175196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174474, d175196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174495 q = 0) : d175217 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174495, d175217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174495, d175217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15925 (p : Pattern) (selected : d174501 p = 0) : d175223 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174496 q = 0) : d175218 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174496, d175218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15919 q selected
    | true =>
      simp only [d174496, d175218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15924 q selected
  have h2 (q : Pattern) (selected : d174497 q = 0) : d175219 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174497, d175219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174497, d175219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174498 q = 0) : d175220 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174498, d175220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174498, d175220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174499 q = 0) : d175221 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174499, d175221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174499, d175221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174500 q = 0) : d175222 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174500, d175222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174500, d175222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174501 q = 0) : d175223 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174501, d175223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174501, d175223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15926 (p : Pattern) (selected : d174507 p = 0) : d175229 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174487 q = 0) : d175209 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174487, d175209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15922 q selected
    | true =>
      simp only [d174487, d175209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174488 q = 0) : d175210 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174488, d175210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174488, d175210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174502 q = 0) : d175224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174502, d175224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15925 q selected
    | true =>
      simp only [d174502, d175224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174503 q = 0) : d175225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174503, d175225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174503, d175225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174504 q = 0) : d175226 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174504, d175226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174504, d175226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174505 q = 0) : d175227 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174505, d175227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174505, d175227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174506 q = 0) : d175228 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174506, d175228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174506, d175228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174507 q = 0) : d175229 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174507, d175229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174507, d175229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15927 (p : Pattern) (selected : d174515 p = 0) : d175176 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2201 q = 0) : d53314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2201, d53314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro587 q selected
    | true =>
      simp only [d2201, d53314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174509 q = 0) : d175171 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174509, d175171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174509, d175171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10458 q = 0) : d101685 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10458, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6772 q selected
    | true =>
      simp only [d10458, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174510 q = 0) : d175172 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174510, d175172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174510, d175172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174511 q = 0) : d175173 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174511, d175173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174511, d175173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10468 q = 0) : d101674 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10468, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6773 q selected
    | true =>
      simp only [d10468, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174512 q = 0) : d175168 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174512, d175168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174512, d175168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10482 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6774 q selected
    | true =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174513 q = 0) : d175174 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174513, d175174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d174513, d175174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d174514 q = 0) : d175175 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174514, d175175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174514, d175175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174515 q = 0) : d175176 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174515, d175176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174515, d175176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15928 (p : Pattern) (selected : d174520 p = 0) : d175189 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2219 q = 0) : d53332 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2219, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro592 q selected
    | true =>
      simp only [d2219, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174516 q = 0) : d175186 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174516, d175186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174516, d175186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10493 q = 0) : d101712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10493, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6776 q selected
    | true =>
      simp only [d10493, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174517 q = 0) : d175187 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174517, d175187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174517, d175187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174518 q = 0) : d175188 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174518, d175188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174518, d175188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10482 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6774 q selected
    | true =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174513 q = 0) : d175174 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174513, d175174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174513, d175174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174519 q = 0) : d175180 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174519, d175180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174519, d175180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174520 q = 0) : d175189 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174520, d175189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174520, d175189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15929 (p : Pattern) (selected : d174528 p = 0) : d175197 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174524 q = 0) : d175193 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174524, d175193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174524, d175193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174525 q = 0) : d175194 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174525, d175194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174525, d175194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10521 q = 0) : d101733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6779 q selected
    | true =>
      simp only [d10521, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174526 q = 0) : d175195 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174526, d175195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174526, d175195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174527 q = 0) : d175196 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174527, d175196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174527, d175196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174528 q = 0) : d175197 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174528, d175197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174528, d175197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15930 (p : Pattern) (selected : d174535 p = 0) : d175217 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2231 q = 0) : d53344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro593 q selected
    | true =>
      simp only [d2231, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174533 q = 0) : d175215 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174533, d175215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174533, d175215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174534 q = 0) : d175216 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174534, d175216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174534, d175216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10521 q = 0) : d101733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6779 q selected
    | true =>
      simp only [d10521, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174526 q = 0) : d175195 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174526, d175195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174526, d175195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174527 q = 0) : d175196 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174527, d175196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174527, d175196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174535 q = 0) : d175217 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174535, d175217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174535, d175217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15931 (p : Pattern) (selected : d174541 p = 0) : d175232 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174521 q = 0) : d175190 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174521, d175190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15927 q selected
    | true =>
      simp only [d174521, d175190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15928 q selected
  have h2 (q : Pattern) (selected : d174522 q = 0) : d175191 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174522, d175191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174522, d175191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174523 q = 0) : d175192 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174523, d175192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174523, d175192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174529 q = 0) : d175198 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174529, d175198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15928 q selected
    | true =>
      simp only [d174529, d175198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15929 q selected
  have h5 (q : Pattern) (selected : d174530 q = 0) : d175199 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174530, d175199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174530, d175199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174531 q = 0) : d175200 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174531, d175200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174531, d175200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174532 q = 0) : d175201 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174532, d175201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174532, d175201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174536 q = 0) : d175218 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174536, d175218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15928 q selected
    | true =>
      simp only [d174536, d175218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15930 q selected
  have h9 (q : Pattern) (selected : d174537 q = 0) : d175219 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174537, d175219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174537, d175219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174538 q = 0) : d175220 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174538, d175220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174538, d175220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174539 q = 0) : d175221 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174539, d175221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174539, d175221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d174540 q = 0) : d175231 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174540, d175231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174540, d175231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d174541 q = 0) : d175232 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174541, d175232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d174541, d175232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro15932 (p : Pattern) (selected : d174545 p = 0) : d175223 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174536 q = 0) : d175218 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174536, d175218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15928 q selected
    | true =>
      simp only [d174536, d175218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15930 q selected
  have h2 (q : Pattern) (selected : d174537 q = 0) : d175219 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174537, d175219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174537, d175219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174538 q = 0) : d175220 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174538, d175220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174538, d175220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174539 q = 0) : d175221 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174539, d175221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174539, d175221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174544 q = 0) : d175222 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174544, d175222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174544, d175222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174545 q = 0) : d175223 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174545, d175223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174545, d175223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15933 (p : Pattern) (selected : d174551 p = 0) : d175238 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174542 q = 0) : d175233 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174542, d175233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15931 q selected
    | true =>
      simp only [d174542, d175233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174543 q = 0) : d175234 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174543, d175234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174543, d175234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174546 q = 0) : d175224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174546, d175224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15932 q selected
    | true =>
      simp only [d174546, d175224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174547 q = 0) : d175225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174547, d175225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174547, d175225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174548 q = 0) : d175235 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174548, d175235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174548, d175235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174549 q = 0) : d175236 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174549, d175236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174549, d175236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174550 q = 0) : d175237 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174550, d175237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174550, d175237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174551 q = 0) : d175238 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174551, d175238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174551, d175238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15934 (p : Pattern) (selected : d174555 p = 0) : d175242 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174546 q = 0) : d175224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174546, d175224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15932 q selected
    | true =>
      simp only [d174546, d175224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174547 q = 0) : d175225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174547, d175225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174547, d175225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174552 q = 0) : d175239 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174552, d175239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174552, d175239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174553 q = 0) : d175240 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174553, d175240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174553, d175240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174554 q = 0) : d175241 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174554, d175241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174554, d175241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174555 q = 0) : d175242 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174555, d175242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174555, d175242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15935 (p : Pattern) (selected : d174558 p = 0) : d175245 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2065 q = 0) : d53344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174493 q = 0) : d175215 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174493, d175215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174493, d175215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174494 q = 0) : d175216 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174494, d175216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174494, d175216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174558 q = 0) : d175245 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174558, d175245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174558, d175245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro15936 (p : Pattern) (selected : d174564 p = 0) : d175251 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174468 q = 0) : d175190 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174468, d175190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15917 q selected
    | true =>
      simp only [d174468, d175190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15919 q selected
  have h2 (q : Pattern) (selected : d174469 q = 0) : d175191 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174469, d175191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174469, d175191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174470 q = 0) : d175192 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174470, d175192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174470, d175192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174476 q = 0) : d175198 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174476, d175198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15919 q selected
    | true =>
      simp only [d174476, d175198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15920 q selected
  have h5 (q : Pattern) (selected : d174477 q = 0) : d175199 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174477, d175199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174477, d175199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174478 q = 0) : d175200 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174478, d175200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174478, d175200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174479 q = 0) : d175201 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174479, d175201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174479, d175201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174559 q = 0) : d175246 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174559, d175246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15919 q selected
    | true =>
      simp only [d174559, d175246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15935 q selected
  have h9 (q : Pattern) (selected : d174560 q = 0) : d175247 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174560, d175247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174560, d175247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174561 q = 0) : d175248 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174561, d175248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174561, d175248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174562 q = 0) : d175249 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174562, d175249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174562, d175249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d174563 q = 0) : d175250 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174563, d175250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174563, d175250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d174564 q = 0) : d175251 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174564, d175251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d174564, d175251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro15937 (p : Pattern) (selected : d174570 p = 0) : d175257 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174565 q = 0) : d175252 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174565, d175252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15936 q selected
    | true =>
      simp only [d174565, d175252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174566 q = 0) : d175253 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174566, d175253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174566, d175253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174567 q = 0) : d175254 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174567, d175254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174567, d175254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174568 q = 0) : d175255 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174568, d175255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174568, d175255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174569 q = 0) : d175256 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174569, d175256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174569, d175256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174570 q = 0) : d175257 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174570, d175257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174570, d175257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15938 (p : Pattern) (selected : d174576 p = 0) : d175263 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174508 q = 0) : d175230 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d174508, d175230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15923 q selected
    | true =>
      simp only [d174508, d175230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15926 q selected
  have h2 (q : Pattern) (selected : d174556 q = 0) : d175243 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d174556, d175243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15933 q selected
    | true =>
      simp only [d174556, d175243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15934 q selected
  have h3 (q : Pattern) (selected : d174557 q = 0) : d175244 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d174557, d175244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174557, d175244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174571 q = 0) : d175258 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d174571, d175258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15937 q selected
    | true =>
      simp only [d174571, d175258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174572 q = 0) : d175259 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d174572, d175259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174572, d175259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174573 q = 0) : d175260 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d174573, d175260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174573, d175260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174574 q = 0) : d175261 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d174574, d175261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174574, d175261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174575 q = 0) : d175262 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d174575, d175262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174575, d175262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d174576 q = 0) : d175263 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d174576, d175263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174576, d175263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15939 (p : Pattern) (selected : d174581 p = 0) : d175242 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174502 q = 0) : d175224 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174502, d175224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15925 q selected
    | true =>
      simp only [d174502, d175224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174503 q = 0) : d175225 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174503, d175225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174503, d175225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174578 q = 0) : d175239 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174578, d175239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174578, d175239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174579 q = 0) : d175240 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174579, d175240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174579, d175240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174580 q = 0) : d175241 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174580, d175241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174580, d175241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174581 q = 0) : d175242 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174581, d175242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174581, d175242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15940 (p : Pattern) (selected : d174587 p = 0) : d175270 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174582 q = 0) : d175265 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d174582, d175265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15939 q selected
    | true =>
      simp only [d174582, d175265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174583 q = 0) : d175266 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d174583, d175266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174583, d175266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174584 q = 0) : d175267 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d174584, d175267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174584, d175267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174585 q = 0) : d175268 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d174585, d175268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174585, d175268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174586 q = 0) : d175269 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d174586, d175269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174586, d175269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174587 q = 0) : d175270 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d174587, d175270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174587, d175270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15941 (p : Pattern) (selected : d174593 p = 0) : d175276 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174577 q = 0) : d175264 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d174577, d175264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174577, d175264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15938 q selected
  have h2 (q : Pattern) (selected : d174588 q = 0) : d175271 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d174588, d175271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174588, d175271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15940 q selected
  have h3 (q : Pattern) (selected : d174589 q = 0) : d175272 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d174589, d175272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174589, d175272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174590 q = 0) : d175273 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d174590, d175273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174590, d175273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174591 q = 0) : d175274 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d174591, d175274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174591, d175274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174592 q = 0) : d175275 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d174592, d175275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174592, d175275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174593 q = 0) : d175276 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d174593, d175276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174593, d175276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15942 (p : Pattern) (selected : d174599 p = 0) : d175282 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174594 q = 0) : d175277 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d174594, d175277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174594, d175277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15941 q selected
  have h2 (q : Pattern) (selected : d174595 q = 0) : d175278 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d174595, d175278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174595, d175278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174596 q = 0) : d175279 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d174596, d175279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174596, d175279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174597 q = 0) : d175280 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d174597, d175280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174597, d175280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174598 q = 0) : d175281 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d174598, d175281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174598, d175281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174599 q = 0) : d175282 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d174599, d175282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174599, d175282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15943 (p : Pattern) (selected : d174605 p = 0) : d175288 p = 1 := by
  have h0 (q : Pattern) (selected : d173995 q = 0) : d174829 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d173995, d174829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15820 q selected
    | true =>
      simp only [d173995, d174829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15838 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d174116 q = 0) : d174915 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d174116, d174915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174116, d174915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15861 q selected
  have h3 (q : Pattern) (selected : d174117 q = 0) : d174916 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d174117, d174916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174117, d174916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174276 q = 0) : d175037 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d174276, d175037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174276, d175037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15888 q selected
  have h5 (q : Pattern) (selected : d174277 q = 0) : d175038 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d174277, d175038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174277, d175038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174278 q = 0) : d175039 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d174278, d175039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174278, d175039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174439 q = 0) : d175161 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d174439, d175161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174439, d175161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15915 q selected
  have h8 (q : Pattern) (selected : d174440 q = 0) : d175162 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d174440, d175162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174440, d175162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d174441 q = 0) : d175163 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d174441, d175163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174441, d175163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174442 q = 0) : d175164 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d174442, d175164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174442, d175164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174600 q = 0) : d175283 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d174600, d175283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174600, d175283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15942 q selected
  have h12 (q : Pattern) (selected : d174601 q = 0) : d175284 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d174601, d175284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174601, d175284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d174602 q = 0) : d175285 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d174602, d175285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174602, d175285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d174603 q = 0) : d175286 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d174603, d175286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174603, d175286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d174604 q = 0) : d175287 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d174604, d175287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174604, d175287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d174605 q = 0) : d175288 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d174605, d175288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d174605, d175288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro15944 (p : Pattern) (selected : d174611 p = 0) : d175294 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174606 q = 0) : d175289 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d174606, d175289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15943 q selected
    | true =>
      simp only [d174606, d175289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174607 q = 0) : d175290 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d174607, d175290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174607, d175290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174608 q = 0) : d175291 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d174608, d175291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174608, d175291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174609 q = 0) : d175292 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d174609, d175292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174609, d175292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174610 q = 0) : d175293 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d174610, d175293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174610, d175293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174611 q = 0) : d175294 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d174611, d175294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174611, d175294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15945 (p : Pattern) (selected : d174617 p = 0) : d175300 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174612 q = 0) : d175295 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d174612, d175295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15944 q selected
    | true =>
      simp only [d174612, d175295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174613 q = 0) : d175296 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d174613, d175296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174613, d175296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174614 q = 0) : d175297 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d174614, d175297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174614, d175297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174615 q = 0) : d175298 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d174615, d175298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174615, d175298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174616 q = 0) : d175299 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d174616, d175299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174616, d175299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174617 q = 0) : d175300 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d174617, d175300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174617, d175300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15946 (p : Pattern) (selected : d174623 p = 0) : d175306 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174618 q = 0) : d175301 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d174618, d175301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15945 q selected
    | true =>
      simp only [d174618, d175301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174619 q = 0) : d175302 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d174619, d175302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174619, d175302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174620 q = 0) : d175303 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d174620, d175303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174620, d175303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174621 q = 0) : d175304 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d174621, d175304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174621, d175304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174622 q = 0) : d175305 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d174622, d175305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174622, d175305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174623 q = 0) : d175306 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d174623, d175306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174623, d175306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15947 (p : Pattern) (selected : d174629 p = 0) : d175312 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174624 q = 0) : d175307 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d174624, d175307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15946 q selected
    | true =>
      simp only [d174624, d175307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174625 q = 0) : d175308 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d174625, d175308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174625, d175308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174626 q = 0) : d175309 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d174626, d175309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174626, d175309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174627 q = 0) : d175310 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d174627, d175310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174627, d175310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174628 q = 0) : d175311 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d174628, d175311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174628, d175311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174629 q = 0) : d175312 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d174629, d175312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174629, d175312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15948 (p : Pattern) (selected : d174635 p = 0) : d175318 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174630 q = 0) : d175313 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d174630, d175313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15947 q selected
    | true =>
      simp only [d174630, d175313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174631 q = 0) : d175314 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d174631, d175314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174631, d175314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174632 q = 0) : d175315 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d174632, d175315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174632, d175315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174633 q = 0) : d175316 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d174633, d175316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174633, d175316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174634 q = 0) : d175317 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d174634, d175317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174634, d175317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174635 q = 0) : d175318 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d174635, d175318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174635, d175318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15949 (p : Pattern) (selected : d174641 p = 0) : d175324 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174636 q = 0) : d175319 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d174636, d175319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15948 q selected
    | true =>
      simp only [d174636, d175319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174637 q = 0) : d175320 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d174637, d175320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174637, d175320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174638 q = 0) : d175321 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d174638, d175321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174638, d175321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174639 q = 0) : d175322 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d174639, d175322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174639, d175322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174640 q = 0) : d175323 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d174640, d175323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174640, d175323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174641 q = 0) : d175324 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d174641, d175324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174641, d175324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15950 (p : Pattern) (selected : d174647 p = 0) : d175330 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d174642 q = 0) : d175325 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d174642, d175325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15949 q selected
    | true =>
      simp only [d174642, d175325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174643 q = 0) : d175326 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d174643, d175326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174643, d175326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174644 q = 0) : d175327 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d174644, d175327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174644, d175327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174645 q = 0) : d175328 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d174645, d175328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174645, d175328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174646 q = 0) : d175329 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d174646, d175329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174646, d175329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174647 q = 0) : d175330 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d174647, d175330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174647, d175330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15951 (p : Pattern) (selected : d173805 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (selected : d173803 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d173804 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d173804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173805 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d173805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro15952 (p : Pattern) (selected : d173811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d173806 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15951 q selected
    | true =>
      simp only [d173806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173807 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173808 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173809 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173810 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173811 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15953 (p : Pattern) (selected : d173817 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d173812 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15952 q selected
    | true =>
      simp only [d173812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173813 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173814 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173815 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173816 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173817 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15954 (p : Pattern) (selected : d173823 p = 1) : d175760 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d173802 q = 1) : d173802 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d173818 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15953 q selected
    | true =>
      simp only [d173818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d173819 q = 1) : d175756 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173819, d175756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173819, d175756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173772 q = 1) : d173772 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d173820 q = 1) : d175757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173820, d175757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173820, d175757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173821 q = 1) : d175758 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173821, d175758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173821, d175758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173822 q = 1) : d175759 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173822, d175759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173822, d175759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173823 q = 1) : d175760 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173823, d175760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173823, d175760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15955 (p : Pattern) (selected : d173829 p = 1) : d175766 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d173824 q = 1) : d175761 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173824, d175761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173824, d175761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15954 q selected
  have h2 (q : Pattern) (selected : d173825 q = 1) : d175762 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173825, d175762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173825, d175762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d173826 q = 1) : d175763 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173826, d175763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173826, d175763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173827 q = 1) : d175764 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173827, d175764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173827, d175764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173828 q = 1) : d175765 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173828, d175765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173828, d175765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173829 q = 1) : d175766 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173829, d175766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173829, d175766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15956 (p : Pattern) (selected : d173855 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (selected : d173853 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173803 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173854 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d173854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173804 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d173804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d173855 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d173855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15957 (p : Pattern) (selected : d173861 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d173856 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15956 q selected
    | true =>
      simp only [d173856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15951 q selected
  have h2 (q : Pattern) (selected : d173857 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173858 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173806 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15951 q selected
    | true =>
      simp only [d173806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173807 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173808 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173859 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173809 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d173860 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d173861 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d173861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15958 (p : Pattern) (selected : d173867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d173862 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15957 q selected
    | true =>
      simp only [d173862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173863 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173812 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15952 q selected
    | true =>
      simp only [d173812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173813 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d173864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173865 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d173866 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d173867 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15959 (p : Pattern) (selected : d173879 p = 1) : d175776 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d173852 q = 1) : d173852 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d173868 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15958 q selected
    | true =>
      simp only [d173868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15953 q selected
  have h3 (q : Pattern) (selected : d173869 q = 1) : d175772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173869, d175772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173869, d175772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173875 q = 1) : d173875 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d173876 q = 1) : d175773 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173876, d175773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173876, d175773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173877 q = 1) : d175774 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173877, d175774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173877, d175774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173878 q = 1) : d175775 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173878, d175775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173878, d175775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173879 q = 1) : d175776 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173879, d175776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173879, d175776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15960 (p : Pattern) (selected : d173891 p = 1) : d175782 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d173880 q = 1) : d175777 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173880, d175777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173880, d175777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15959 q selected
  have h2 (q : Pattern) (selected : d173886 q = 1) : d173886 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d173887 q = 1) : d175778 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173887, d175778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173887, d175778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173888 q = 1) : d175779 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173888, d175779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173888, d175779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173889 q = 1) : d175780 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173889, d175780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173889, d175780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173890 q = 1) : d175781 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173890, d175781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173890, d175781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d173891 q = 1) : d175782 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173891, d175782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173891, d175782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15961 (p : Pattern) (selected : d173897 p = 1) : d175788 p = 1 := by
  have h0 (q : Pattern) (selected : d173786 q = 1) : d173786 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d173830 q = 1) : d175767 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173830, d175767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173830, d175767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15955 q selected
  have h3 (q : Pattern) (selected : d173831 q = 1) : d175768 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173831, d175768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173831, d175768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173832 q = 1) : d175769 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173832, d175769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173832, d175769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d173833 q = 1) : d175770 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173833, d175770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173833, d175770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173834 q = 1) : d175771 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173834, d175771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173834, d175771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173892 q = 1) : d175783 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173892, d175783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173892, d175783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15960 q selected
  have h8 (q : Pattern) (selected : d173893 q = 1) : d175784 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173893, d175784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173893, d175784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d173894 q = 1) : d175785 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173894, d175785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173894, d175785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d173895 q = 1) : d175786 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173895, d175786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173895, d175786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d173896 q = 1) : d175787 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173896, d175787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173896, d175787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d173897 q = 1) : d175788 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173897, d175788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173897, d175788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro15962 (p : Pattern) (selected : d173938 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (selected : d173934 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d350 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
    | true =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173853 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173935 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d173935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6813 q selected
    | true =>
      simp only [d9512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d173936 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d173803 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d173803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d173937 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d173937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d173938 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d173938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15963 (p : Pattern) (selected : d173945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d173939 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15962 q selected
    | true =>
      simp only [d173939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15956 q selected
  have h2 (q : Pattern) (selected : d173940 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173941 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173856 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15956 q selected
    | true =>
      simp only [d173856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15951 q selected
  have h5 (q : Pattern) (selected : d173857 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173858 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173942 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173943 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d173944 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d173945 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d173945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15964 (p : Pattern) (selected : d173949 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d173856 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d173856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15956 q selected
    | true =>
      simp only [d173856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15951 q selected
  have h2 (q : Pattern) (selected : d173857 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d173857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173858 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d173858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173943 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d173943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173948 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173949 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15965 (p : Pattern) (selected : d173955 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d173946 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15963 q selected
    | true =>
      simp only [d173946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173947 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173950 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15964 q selected
    | true =>
      simp only [d173950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173951 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d173952 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173953 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d173954 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d173954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d173955 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15966 (p : Pattern) (selected : d173959 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d173950 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15964 q selected
    | true =>
      simp only [d173950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d173951 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173956 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d173956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d173957 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173958 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173959 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15967 (p : Pattern) (selected : d173971 p = 1) : d175793 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d173933 q = 1) : d173933 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d173960 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15965 q selected
    | true =>
      simp only [d173960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15966 q selected
  have h3 (q : Pattern) (selected : d173961 q = 1) : d175789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173961, d175789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173961, d175789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173967 q = 1) : d173967 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d173968 q = 1) : d175790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173968, d175790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173968, d175790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173969 q = 1) : d175791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173969, d175791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173969, d175791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d173970 q = 1) : d175792 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173970, d175792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173970, d175792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173971 q = 1) : d175793 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173971, d175793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173971, d175793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15968 (p : Pattern) (selected : d173988 p = 1) : d175799 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d173972 q = 1) : d175794 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173972, d175794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173972, d175794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15967 q selected
  have h2 (q : Pattern) (selected : d173983 q = 1) : d173983 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d173984 q = 1) : d175795 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173984, d175795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173984, d175795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173985 q = 1) : d175796 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173985, d175796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173985, d175796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d173986 q = 1) : d175797 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173986, d175797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d173986, d175797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d173987 q = 1) : d175798 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173987, d175798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d173987, d175798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d173988 q = 1) : d175799 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173988, d175799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173988, d175799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15969 (p : Pattern) (selected : d173994 p = 1) : d175805 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d173989 q = 1) : d175800 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173989, d175800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173989, d175800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15968 q selected
  have h2 (q : Pattern) (selected : d173990 q = 1) : d175801 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173990, d175801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173990, d175801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d173991 q = 1) : d175802 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173991, d175802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173991, d175802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173992 q = 1) : d175803 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173992, d175803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173992, d175803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d173993 q = 1) : d175804 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173993, d175804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173993, d175804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d173994 q = 1) : d175805 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173994, d175805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d173994, d175805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15970 (p : Pattern) (selected : d174052 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174046 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9661 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6823 q selected
    | true =>
      simp only [d9661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174048 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9671 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6824 q selected
    | true =>
      simp only [d9671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174049 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d874 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174050 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d174050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d174051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174052 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15971 (p : Pattern) (selected : d174055 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (selected : d173934 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d173934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d874 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174050 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174053 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174054 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174055 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15972 (p : Pattern) (selected : d174059 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174050 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174054 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174059 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro15973 (p : Pattern) (selected : d174066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174056 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15970 q selected
    | true =>
      simp only [d174056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15971 q selected
  have h2 (q : Pattern) (selected : d174057 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174058 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174060 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15971 q selected
    | true =>
      simp only [d174060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15972 q selected
  have h5 (q : Pattern) (selected : d174061 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174062 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174063 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174064 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174065 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174066 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d174066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro15974 (p : Pattern) (selected : d174070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174060 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15971 q selected
    | true =>
      simp only [d174060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15972 q selected
  have h2 (q : Pattern) (selected : d174061 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174062 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174064 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174069 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174070 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15975 (p : Pattern) (selected : d174076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174067 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15973 q selected
    | true =>
      simp only [d174067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174068 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15974 q selected
    | true =>
      simp only [d174071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174075 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174076 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15976 (p : Pattern) (selected : d174080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15974 q selected
    | true =>
      simp only [d174071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174077 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174078 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174079 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174080 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15977 (p : Pattern) (selected : d174092 p = 1) : d175811 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174045 q = 1) : d174045 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d174081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d174081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15975 q selected
    | true =>
      simp only [d174081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15976 q selected
  have h3 (q : Pattern) (selected : d174082 q = 1) : d175807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d174082, d175807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174082, d175807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174088 q = 1) : d174088 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d174089 q = 1) : d175808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d174089, d175808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174089, d175808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174090 q = 1) : d175809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d174090, d175809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174090, d175809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174091 q = 1) : d175810 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d174091, d175810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174091, d175810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174092 q = 1) : d175811 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d174092, d175811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174092, d175811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15978 (p : Pattern) (selected : d174109 p = 1) : d175817 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174093 q = 1) : d175812 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d174093, d175812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174093, d175812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15977 q selected
  have h2 (q : Pattern) (selected : d174104 q = 1) : d174104 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d174105 q = 1) : d175813 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d174105, d175813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174105, d175813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174106 q = 1) : d175814 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d174106, d175814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174106, d175814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174107 q = 1) : d175815 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d174107, d175815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174107, d175815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174108 q = 1) : d175816 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d174108, d175816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174108, d175816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174109 q = 1) : d175817 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d174109, d175817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174109, d175817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15979 (p : Pattern) (selected : d174115 p = 1) : d175823 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174110 q = 1) : d175818 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d174110, d175818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174110, d175818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15978 q selected
  have h2 (q : Pattern) (selected : d174111 q = 1) : d175819 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d174111, d175819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174111, d175819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174112 q = 1) : d175820 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d174112, d175820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174112, d175820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174113 q = 1) : d175821 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d174113, d175821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174113, d175821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174114 q = 1) : d175822 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d174114, d175822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174114, d175822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174115 q = 1) : d175823 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d174115, d175823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174115, d175823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15980 (p : Pattern) (selected : d174192 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174186 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6837 q selected
    | true =>
      simp only [d9896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174187 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174188 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9908 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6838 q selected
    | true =>
      simp only [d9908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174189 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
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
  have h9 (q : Pattern) (selected : d174190 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d174190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d174191 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174192 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15981 (p : Pattern) (selected : d174197 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174193 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1276 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
    | true =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174194 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174195 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d9918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6839 q selected
    | true =>
      simp only [d9918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174190 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174196 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174197 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15982 (p : Pattern) (selected : d174205 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174201 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174202 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9952 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6843 q selected
    | true =>
      simp only [d9952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174203 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174204 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174205 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15983 (p : Pattern) (selected : d174211 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174194 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174210 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9952 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6843 q selected
    | true =>
      simp only [d9952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174203 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174204 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174211 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15984 (p : Pattern) (selected : d174217 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174198 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15980 q selected
    | true =>
      simp only [d174198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15981 q selected
  have h2 (q : Pattern) (selected : d174199 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174200 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174206 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15981 q selected
    | true =>
      simp only [d174206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15982 q selected
  have h5 (q : Pattern) (selected : d174207 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174208 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174209 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174212 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15981 q selected
    | true =>
      simp only [d174212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15983 q selected
  have h9 (q : Pattern) (selected : d174213 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174214 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174215 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d174216 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d174217 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d174217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro15985 (p : Pattern) (selected : d174221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174212 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15981 q selected
    | true =>
      simp only [d174212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15983 q selected
  have h2 (q : Pattern) (selected : d174213 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174214 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174215 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174220 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174221 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15986 (p : Pattern) (selected : d174227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174218 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15984 q selected
    | true =>
      simp only [d174218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174219 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174222 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15985 q selected
    | true =>
      simp only [d174222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174223 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174224 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174225 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174226 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174227 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15987 (p : Pattern) (selected : d174231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174222 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15985 q selected
    | true =>
      simp only [d174222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174223 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174228 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174229 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174230 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174231 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15988 (p : Pattern) (selected : d174252 p = 1) : d175830 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174185 q = 1) : d174185 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d174232 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d174232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15986 q selected
    | true =>
      simp only [d174232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15987 q selected
  have h3 (q : Pattern) (selected : d174233 q = 1) : d175826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d174233, d175826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174233, d175826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174248 q = 1) : d174248 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d174249 q = 1) : d175827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d174249, d175827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174249, d175827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174250 q = 1) : d175828 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d174250, d175828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174250, d175828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174251 q = 1) : d175829 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d174251, d175829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174251, d175829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174252 q = 1) : d175830 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d174252, d175830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174252, d175830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro15989 (p : Pattern) (selected : d174269 p = 1) : d175836 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174253 q = 1) : d175831 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d174253, d175831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174253, d175831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15988 q selected
  have h2 (q : Pattern) (selected : d174264 q = 1) : d174264 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d174265 q = 1) : d175832 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d174265, d175832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174265, d175832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174266 q = 1) : d175833 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d174266, d175833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174266, d175833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174267 q = 1) : d175834 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d174267, d175834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174267, d175834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174268 q = 1) : d175835 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d174268, d175835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174268, d175835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174269 q = 1) : d175836 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d174269, d175836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174269, d175836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15990 (p : Pattern) (selected : d174275 p = 1) : d175842 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174270 q = 1) : d175837 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d174270, d175837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174270, d175837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15989 q selected
  have h2 (q : Pattern) (selected : d174271 q = 1) : d175838 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d174271, d175838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174271, d175838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174272 q = 1) : d175839 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d174272, d175839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174272, d175839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174273 q = 1) : d175840 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d174273, d175840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174273, d175840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174274 q = 1) : d175841 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d174274, d175841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174274, d175841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174275 q = 1) : d175842 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d174275, d175842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174275, d175842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro15991 (p : Pattern) (selected : d174354 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174348 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10190 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6855 q selected
    | true =>
      simp only [d10190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174349 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174350 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10200 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6856 q selected
    | true =>
      simp only [d10200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174351 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
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
  have h9 (q : Pattern) (selected : d174352 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d174352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d174353 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174354 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro15992 (p : Pattern) (selected : d174359 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174355 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10226 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6859 q selected
    | true =>
      simp only [d10226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174356 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174357 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10215 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6857 q selected
    | true =>
      simp only [d10215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174352 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174358 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d174359 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro15993 (p : Pattern) (selected : d174367 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174363 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174364 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10255 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6862 q selected
    | true =>
      simp only [d10255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174365 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174366 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174367 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15994 (p : Pattern) (selected : d174374 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (selected : d174372 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d174373 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10255 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6862 q selected
    | true =>
      simp only [d10255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174365 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d174365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174366 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174374 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d174374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro15995 (p : Pattern) (selected : d174380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174360 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15991 q selected
    | true =>
      simp only [d174360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15992 q selected
  have h2 (q : Pattern) (selected : d174361 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174362 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174368 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15992 q selected
    | true =>
      simp only [d174368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15993 q selected
  have h5 (q : Pattern) (selected : d174369 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174370 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174371 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174375 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15992 q selected
    | true =>
      simp only [d174375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15994 q selected
  have h9 (q : Pattern) (selected : d174376 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d174377 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d174378 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d174378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d174379 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d174380 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d174380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro15996 (p : Pattern) (selected : d174384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174375 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15992 q selected
    | true =>
      simp only [d174375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15994 q selected
  have h2 (q : Pattern) (selected : d174376 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174377 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174378 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174383 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174384 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d174384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15997 (p : Pattern) (selected : d174390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174381 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15995 q selected
    | true =>
      simp only [d174381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174382 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174385 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15996 q selected
    | true =>
      simp only [d174385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174386 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d174387 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174388 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d174389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d174389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d174390 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d174390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro15998 (p : Pattern) (selected : d174394 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174385 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d174385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15996 q selected
    | true =>
      simp only [d174385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d174386 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d174386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d174391 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d174391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d174391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d174392 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d174392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174393 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d174393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d174394 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d174394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d174394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro15999 (p : Pattern) (selected : d174415 p = 1) : d175850 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d174347 q = 1) : d174347 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d174395 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d174395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15997 q selected
    | true =>
      simp only [d174395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15998 q selected
  have h3 (q : Pattern) (selected : d174396 q = 1) : d175846 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d174396, d175846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d174396, d175846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d174411 q = 1) : d174411 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d174412 q = 1) : d175847 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d174412, d175847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d174412, d175847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d174413 q = 1) : d175848 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d174413, d175848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174413, d175848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d174414 q = 1) : d175849 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d174414, d175849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174414, d175849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d174415 q = 1) : d175850 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d174415, d175850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d174415, d175850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
end NetHack.Soko22Hazard87
