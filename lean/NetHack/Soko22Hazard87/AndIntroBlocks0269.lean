import NetHack.Soko22Hazard87.AndIntroBlocks0268
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro67250 (p : Pattern) (ha : d237117 p = 1) (hb : d266934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237097 q = 1) (hb : d266920 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237097, d266920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67245 q ha hb
    | true =>
      simp only [d237097, d266920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67247 q ha hb
  have h2 (q : Pattern) (ha : d237098 q = 1) (hb : d266921 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237098, d266921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237098, d266921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237099 q = 1) (hb : d266922 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237099, d266922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237099, d266922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237107 q = 1) (hb : d266924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237107, d266924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67247 q ha hb
    | true =>
      simp only [d237107, d266924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67248 q ha hb
  have h5 (q : Pattern) (ha : d237108 q = 1) (hb : d266925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237108, d266925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237108, d266925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237109 q = 1) (hb : d266926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237109, d266926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237109, d266926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237110 q = 1) (hb : d266927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237110, d266927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237110, d266927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237115 q = 1) (hb : d266932 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237115, d266932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237115, d266932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237116 q = 1) (hb : d266933 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237116, d266933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237116, d266933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237117 q = 1) (hb : d266934 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237117, d266934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237117, d266934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro67251 (p : Pattern) (ha : d237123 p = 1) (hb : d266940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237113 q = 1) (hb : d266930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237113, d266930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67249 q ha hb
    | true =>
      simp only [d237113, d266930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237114 q = 1) (hb : d266931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237114, d266931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237114, d266931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237118 q = 1) (hb : d266935 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237118, d266935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67250 q ha hb
    | true =>
      simp only [d237118, d266935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237119 q = 1) (hb : d266936 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237119, d266936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237119, d266936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237120 q = 1) (hb : d266937 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237120, d266937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237120, d266937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237121 q = 1) (hb : d266938 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237121, d266938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237121, d266938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237122 q = 1) (hb : d266939 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237122, d266939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237122, d266939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237123 q = 1) (hb : d266940 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237123, d266940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237123, d266940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro67252 (p : Pattern) (ha : d237125 p = 1) (hb : d266942 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237107 q = 1) (hb : d266924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237107, d266924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67247 q ha hb
    | true =>
      simp only [d237107, d266924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67248 q ha hb
  have h2 (q : Pattern) (ha : d237108 q = 1) (hb : d266925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237108, d266925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237108, d266925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237109 q = 1) (hb : d266926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237109, d266926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237109, d266926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237115 q = 1) (hb : d266932 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237115, d266932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237115, d266932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237124 q = 1) (hb : d266941 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237124, d266941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237124, d266941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237125 q = 1) (hb : d266942 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237125, d266942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237125, d266942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67253 (p : Pattern) (ha : d237131 p = 1) (hb : d266948 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237118 q = 1) (hb : d266935 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237118, d266935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67250 q ha hb
    | true =>
      simp only [d237118, d266935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237119 q = 1) (hb : d266936 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237119, d266936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237119, d266936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237126 q = 1) (hb : d266943 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237126, d266943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67252 q ha hb
    | true =>
      simp only [d237126, d266943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237127 q = 1) (hb : d266944 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237127, d266944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237127, d266944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237128 q = 1) (hb : d266945 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237128, d266945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237128, d266945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237129 q = 1) (hb : d266946 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237129, d266946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237129, d266946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237130 q = 1) (hb : d266947 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237130, d266947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237130, d266947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237131 q = 1) (hb : d266948 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237131, d266948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237131, d266948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro67254 (p : Pattern) (ha : d237139 p = 1) (hb : d266951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237091 q = 1) (hb : d266903 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237091, d266903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237091, d266903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67207 q ha hb
  have h2 (q : Pattern) (ha : d236889 q = 1) (hb : d266735 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d236889, d266735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67207 q ha hb
    | true =>
      simp only [d236889, d266735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237092 q = 1) (hb : d266904 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237092, d266904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237092, d266904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d236890 q = 1) (hb : d266736 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d236890, d266736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d236890, d266736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237093 q = 1) (hb : d266905 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237093, d266905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237093, d266905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237094 q = 1) (hb : d266906 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237094, d266906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237094, d266906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237100 q = 1) (hb : d266912 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237100, d266912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237100, d266912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237139 q = 1) (hb : d266951 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237139, d266951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237139, d266951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro67255 (p : Pattern) (ha : d237145 p = 1) (hb : d266957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237097 q = 1) (hb : d266920 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237097, d266920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67245 q ha hb
    | true =>
      simp only [d237097, d266920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67247 q ha hb
  have h2 (q : Pattern) (ha : d237098 q = 1) (hb : d266921 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237098, d266921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237098, d266921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237099 q = 1) (hb : d266922 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237099, d266922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237099, d266922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237107 q = 1) (hb : d266924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237107, d266924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67247 q ha hb
    | true =>
      simp only [d237107, d266924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67248 q ha hb
  have h5 (q : Pattern) (ha : d237108 q = 1) (hb : d266925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237108, d266925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237108, d266925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237109 q = 1) (hb : d266926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237109, d266926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237109, d266926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237110 q = 1) (hb : d266927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237110, d266927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237110, d266927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237140 q = 1) (hb : d266952 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237140, d266952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67247 q ha hb
    | true =>
      simp only [d237140, d266952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67254 q ha hb
  have h9 (q : Pattern) (ha : d237141 q = 1) (hb : d266953 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237141, d266953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237141, d266953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237142 q = 1) (hb : d266954 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237142, d266954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237142, d266954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237143 q = 1) (hb : d266955 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237143, d266955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237143, d266955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237144 q = 1) (hb : d266956 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237144, d266956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237144, d266956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237145 q = 1) (hb : d266957 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237145, d266957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237145, d266957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro67256 (p : Pattern) (ha : d237151 p = 1) (hb : d266963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237146 q = 1) (hb : d266958 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237146, d266958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67255 q ha hb
    | true =>
      simp only [d237146, d266958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237147 q = 1) (hb : d266959 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237147, d266959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237147, d266959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237148 q = 1) (hb : d266960 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237148, d266960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237148, d266960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237149 q = 1) (hb : d266961 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237149, d266961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237149, d266961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237150 q = 1) (hb : d266962 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237150, d266962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237150, d266962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237151 q = 1) (hb : d266963 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237151, d266963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237151, d266963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67257 (p : Pattern) (ha : d237157 p = 1) (hb : d266969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237132 q = 1) (hb : d266949 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237132, d266949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67251 q ha hb
    | true =>
      simp only [d237132, d266949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67253 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237137 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d237138 q = 1) (hb : d266950 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237138, d266950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237138, d266950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d237152 q = 1) (hb : d266964 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237152, d266964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67256 q ha hb
    | true =>
      simp only [d237152, d266964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237153 q = 1) (hb : d266965 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237153, d266965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237153, d266965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237154 q = 1) (hb : d266966 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237154, d266966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237154, d266966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237155 q = 1) (hb : d266967 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237155, d266967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237155, d266967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237156 q = 1) (hb : d266968 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237156, d266968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237156, d266968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237157 q = 1) (hb : d266969 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237157, d266969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237157, d266969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro67258 (p : Pattern) (ha : d237136 p = 1) (hb : d266974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237126 q = 1) (hb : d266943 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237126, d266943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67252 q ha hb
    | true =>
      simp only [d237126, d266943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237127 q = 1) (hb : d266944 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237127, d266944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237127, d266944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237133 q = 1) (hb : d266971 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237133, d266971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237133, d266971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237134 q = 1) (hb : d266972 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237134, d266972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237134, d266972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237135 q = 1) (hb : d266973 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237135, d266973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237135, d266973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237136 q = 1) (hb : d266974 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237136, d266974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237136, d266974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67259 (p : Pattern) (ha : d237164 p = 1) (hb : d266980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237159 q = 1) (hb : d266975 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237159, d266975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67258 q ha hb
    | true =>
      simp only [d237159, d266975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237160 q = 1) (hb : d266976 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237160, d266976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237160, d266976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237161 q = 1) (hb : d266977 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237161, d266977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237161, d266977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237162 q = 1) (hb : d266978 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237162, d266978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237162, d266978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237163 q = 1) (hb : d266979 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237163, d266979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237163, d266979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237164 q = 1) (hb : d266980 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237164, d266980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237164, d266980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67260 (p : Pattern) (ha : d237170 p = 1) (hb : d266986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236936 q = 1) (hb : d266775 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d236936, d266775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236936, d266775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67215 q ha hb
  have h2 (q : Pattern) (ha : d236937 q = 1) (hb : d266776 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d236937, d266776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236937, d266776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d236946 q = 1) (hb : d266785 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d236946, d266785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67215 q ha hb
    | true =>
      simp only [d236946, d266785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67218 q ha hb
  have h4 (q : Pattern) (ha : d236947 q = 1) (hb : d266786 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d236947, d266786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236947, d266786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d236948 q = 1) (hb : d266787 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236948, d266787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d236948, d266787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237039 q = 1) (hb : d266870 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237039, d266870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67232 q ha hb
    | true =>
      simp only [d237039, d266870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67239 q ha hb
  have h7 (q : Pattern) (ha : d237052 q = 1) (hb : d266883 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237052, d266883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67240 q ha hb
    | true =>
      simp only [d237052, d266883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67241 q ha hb
  have h8 (q : Pattern) (ha : d237053 q = 1) (hb : d266884 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237053, d266884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237053, d266884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237054 q = 1) (hb : d266885 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237054, d266885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237054, d266885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d237055 q = 1) (hb : d266886 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237055, d266886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237055, d266886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237059 q = 1) (hb : d266890 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237059, d266890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237059, d266890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67242 q ha hb
  have h12 (q : Pattern) (ha : d237061 q = 1) (hb : d266892 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237061, d266892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237061, d266892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67243 q ha hb
  have h13 (q : Pattern) (ha : d237062 q = 1) (hb : d266893 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237062, d266893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237062, d266893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237063 q = 1) (hb : d266894 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237063, d266894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237063, d266894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d237064 q = 1) (hb : d266895 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237064, d266895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d237064, d266895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d237065 q = 1) (hb : d266896 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237065, d266896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237065, d266896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237158 q = 1) (hb : d266970 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237158, d266970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237158, d266970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67257 q ha hb
  have h18 (q : Pattern) (ha : d237165 q = 1) (hb : d266981 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237165, d266981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237165, d266981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67259 q ha hb
  have h19 (q : Pattern) (ha : d237166 q = 1) (hb : d266982 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237166, d266982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d237166, d266982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d237167 q = 1) (hb : d266983 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237167, d266983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d237167, d266983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d237168 q = 1) (hb : d266984 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237168, d266984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d237168, d266984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d237169 q = 1) (hb : d266985 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237169, d266985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d237169, d266985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d237170 q = 1) (hb : d266986 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d237170, d266986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237170, d266986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro67261 (p : Pattern) (ha : d237176 p = 1) (hb : d266992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237171 q = 1) (hb : d266987 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d237171, d266987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237171, d266987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67260 q ha hb
  have h2 (q : Pattern) (ha : d237172 q = 1) (hb : d266988 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d237172, d266988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237172, d266988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237173 q = 1) (hb : d266989 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d237173, d266989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237173, d266989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237174 q = 1) (hb : d266990 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d237174, d266990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237174, d266990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237175 q = 1) (hb : d266991 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d237175, d266991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237175, d266991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237176 q = 1) (hb : d266992 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d237176, d266992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237176, d266992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67262 (p : Pattern) (ha : d237191 p = 1) (hb : d266999 p = 1) : d0 p = 1 := by
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
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d237181 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10042 q = 1) (hb : d237182 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10042, d237182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10042, d237182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10043 q = 1) (hb : d237183 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10043, d237183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10043, d237183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10044 q = 1) (hb : d237184 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10044, d237184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10044, d237184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29527 q = 1) (hb : d237180 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d29527, d237180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d29527, d237180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29528 q = 1) (hb : d237181 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d29528, d237181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29528, d237181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d237186 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d237187 q = 1) (hb : d266996 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d237187, d266996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d237187, d266996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d237188 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d237189 q = 1) (hb : d266997 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d237189, d266997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237189, d266997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d237190 q = 1) (hb : d266998 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d237190, d266998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237190, d266998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d237191 q = 1) (hb : d266999 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d237191, d266999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d237191, d266999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro67263 (p : Pattern) (ha : d237202 p = 1) (hb : d267009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29527 q = 1) (hb : d237180 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d29527, d237180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d29527, d237180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29528 q = 1) (hb : d237181 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d29528, d237181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29528, d237181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d237186 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d237187 q = 1) (hb : d266996 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d237187, d266996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d237187, d266996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d28880 q = 1) (hb : d236725 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28880, d236725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63296 q ha hb
    | true =>
      simp only [d28880, d236725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28881 q = 1) (hb : d236726 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28881, d236726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28881, d236726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d237196 q = 1) (hb : d251925 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d237196, d251925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d237196, d251925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d237197 q = 1) (hb : d267004 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d237197, d267004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237197, d267004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237198 q = 1) (hb : d267005 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d237198, d267005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237198, d267005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d29532 q = 1) (hb : d237185 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d29532, d237185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d29532, d237185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d29533 q = 1) (hb : d237186 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d29533, d237186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d29533, d237186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d237199 q = 1) (hb : d267006 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d237199, d267006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d237199, d267006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h14 (q : Pattern) (ha : d237200 q = 1) (hb : d267007 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d237200, d267007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237200, d267007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d237201 q = 1) (hb : d267008 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d237201, d267008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d237201, d267008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d237202 q = 1) (hb : d267009 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d237202, d267009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237202, d267009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro67264 (p : Pattern) (ha : d237210 p = 1) (hb : d267015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29527 q = 1) (hb : d237180 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d29527, d237180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d29527, d237180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29528 q = 1) (hb : d237181 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d29528, d237181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29528, d237181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d237186 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d237187 q = 1) (hb : d266996 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d237187, d266996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d237187, d266996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d237208 q = 1) (hb : d266997 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d237208, d266997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237208, d266997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237209 q = 1) (hb : d266998 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d237209, d266998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237209, d266998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d29532 q = 1) (hb : d237185 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d29532, d237185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d29532, d237185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29533 q = 1) (hb : d237186 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d29533, d237186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29533, d237186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d237199 q = 1) (hb : d267006 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d237199, d267006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d237199, d267006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d237200 q = 1) (hb : d267007 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d237200, d267007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237200, d267007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237201 q = 1) (hb : d267008 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d237201, d267008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237201, d267008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237210 q = 1) (hb : d267015 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d237210, d267015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237210, d267015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro67265 (p : Pattern) (ha : d237220 p = 1) (hb : d267022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29532 q = 1) (hb : d237185 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d29532, d237185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d29532, d237185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29533 q = 1) (hb : d237186 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d29533, d237186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29533, d237186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d237199 q = 1) (hb : d267006 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d237199, d267006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d237199, d267006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d25765 q = 1) (hb : d52990 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25765, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62639 q ha hb
    | true =>
      simp only [d25765, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25766 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25766, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25766, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25767 q = 1) (hb : d101508 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25767, d101508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25767, d101508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d237215 q = 1) (hb : d267020 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d237215, d267020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237215, d267020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d237216 q = 1) (hb : d267021 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d237216, d267021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237216, d267021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d237217 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10129 q = 1) (hb : d101556 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10129, d101556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro206 q ha hb
    | true =>
      simp only [d10129, d101556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10130 q = 1) (hb : d101557 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10130, d101557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10130, d101557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10131 q = 1) (hb : d101558 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10131, d101558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10131, d101558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d29593 q = 1) (hb : d237218 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29593, d237218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29593, d237218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d29594 q = 1) (hb : d237219 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29594, d237219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d29594, d237219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d237220 q = 1) (hb : d267022 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d237220, d267022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237220, d267022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro67266 (p : Pattern) (ha : d237226 p = 1) (hb : d267028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237192 q = 1) (hb : d267000 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237192, d267000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67262 q ha hb
    | true =>
      simp only [d237192, d267000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237193 q = 1) (hb : d267001 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237193, d267001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237193, d267001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237194 q = 1) (hb : d267002 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237194, d267002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237194, d267002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237195 q = 1) (hb : d267003 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237195, d267003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237195, d267003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237203 q = 1) (hb : d267010 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237203, d267010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67263 q ha hb
    | true =>
      simp only [d237203, d267010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237204 q = 1) (hb : d267011 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237204, d267011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237204, d267011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237205 q = 1) (hb : d267012 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237205, d267012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237205, d267012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237206 q = 1) (hb : d267013 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237206, d267013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237206, d267013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237207 q = 1) (hb : d267014 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237207, d267014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237207, d267014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237211 q = 1) (hb : d267016 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237211, d267016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67264 q ha hb
    | true =>
      simp only [d237211, d267016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237212 q = 1) (hb : d267017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237212, d267017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237212, d267017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237213 q = 1) (hb : d267018 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237213, d267018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237213, d267018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237214 q = 1) (hb : d267019 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237214, d267019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237214, d267019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d237221 q = 1) (hb : d267023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237221, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67265 q ha hb
    | true =>
      simp only [d237221, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d237222 q = 1) (hb : d267024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237222, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d237222, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d237223 q = 1) (hb : d267025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237223, d267025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237223, d267025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237224 q = 1) (hb : d267026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237224, d267026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237224, d267026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d237225 q = 1) (hb : d267027 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237225, d267027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237225, d267027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d237226 q = 1) (hb : d267028 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237226, d267028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237226, d267028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro67267 (p : Pattern) (ha : d237229 p = 1) (hb : d267029 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29527 q = 1) (hb : d237180 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d29527, d237180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d29527, d237180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29528 q = 1) (hb : d237181 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d29528, d237181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29528, d237181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d237186 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d237187 q = 1) (hb : d266996 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d237187, d266996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d237187, d266996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d28880 q = 1) (hb : d236725 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28880, d236725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63296 q ha hb
    | true =>
      simp only [d28880, d236725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28881 q = 1) (hb : d236726 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28881, d236726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28881, d236726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d237196 q = 1) (hb : d251925 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d237196, d251925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d237196, d251925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d237197 q = 1) (hb : d267004 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d237197, d267004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237197, d267004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237198 q = 1) (hb : d267005 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d237198, d267005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237198, d267005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d29532 q = 1) (hb : d237185 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d29532, d237185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d29532, d237185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d29533 q = 1) (hb : d237186 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d29533, d237186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d29533, d237186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d237199 q = 1) (hb : d267006 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d237199, d267006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d237199, d267006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h14 (q : Pattern) (ha : d25765 q = 1) (hb : d52990 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25765, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62639 q ha hb
    | true =>
      simp only [d25765, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d25766 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25766, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d25766, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d25767 q = 1) (hb : d53007 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25767, d53007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25767, d53007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d237227 q = 1) (hb : d267020 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d237227, d267020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237227, d267020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d237228 q = 1) (hb : d267021 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d237228, d267021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d237228, d267021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d237229 q = 1) (hb : d267029 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d237229, d267029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237229, d267029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro67268 (p : Pattern) (ha : d237234 p = 1) (hb : d267022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29532 q = 1) (hb : d237185 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d29532, d237185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d29532, d237185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29533 q = 1) (hb : d237186 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d29533, d237186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29533, d237186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d237199 q = 1) (hb : d267006 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d237199, d267006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d237199, d267006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d25765 q = 1) (hb : d52990 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25765, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62639 q ha hb
    | true =>
      simp only [d25765, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25766 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25766, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25766, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25767 q = 1) (hb : d53007 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25767, d53007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25767, d53007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237227 q = 1) (hb : d267020 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d237227, d267020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237227, d267020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d237228 q = 1) (hb : d267021 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d237228, d267021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237228, d267021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d237217 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d10129 q = 1) (hb : d101556 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10129, d101556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro206 q ha hb
    | true =>
      simp only [d10129, d101556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d10130 q = 1) (hb : d101557 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10130, d101557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10130, d101557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10131 q = 1) (hb : d101558 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10131, d101558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10131, d101558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d29593 q = 1) (hb : d237218 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29593, d237218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d29593, d237218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d29594 q = 1) (hb : d237219 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29594, d237219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d29594, d237219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d237234 q = 1) (hb : d267022 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d237234, d267022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237234, d267022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  exact h18 p ha hb
theorem andIntro67269 (p : Pattern) (ha : d237241 p = 1) (hb : d267036 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237230 q = 1) (hb : d267030 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237230, d267030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67267 q ha hb
    | true =>
      simp only [d237230, d267030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237231 q = 1) (hb : d267031 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237231, d267031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237231, d267031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237232 q = 1) (hb : d267032 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237232, d267032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237232, d267032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237233 q = 1) (hb : d267033 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237233, d267033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237233, d267033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237235 q = 1) (hb : d267023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237235, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67268 q ha hb
    | true =>
      simp only [d237235, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237236 q = 1) (hb : d267024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237236, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237236, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237237 q = 1) (hb : d267025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237237, d267025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237237, d267025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237238 q = 1) (hb : d267026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237238, d267026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237238, d267026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237239 q = 1) (hb : d267034 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237239, d267034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237239, d267034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237221 q = 1) (hb : d267023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237221, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67265 q ha hb
    | true =>
      simp only [d237221, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237222 q = 1) (hb : d267024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237222, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237222, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237223 q = 1) (hb : d267025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237223, d267025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237223, d267025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237224 q = 1) (hb : d267026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237224, d267026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237224, d267026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d237240 q = 1) (hb : d267035 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237240, d267035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237240, d267035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d237241 q = 1) (hb : d267036 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237241, d267036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237241, d267036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro67270 (p : Pattern) (ha : d29595 p = 1) (hb : d237248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10129 q = 1) (hb : d101556 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10129, d101556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro206 q ha hb
    | true =>
      simp only [d10129, d101556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10130 q = 1) (hb : d101557 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10130, d101557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10130, d101557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10131 q = 1) (hb : d101558 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10131, d101558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10131, d101558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29593 q = 1) (hb : d237246 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29593, d237246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29593, d237246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29594 q = 1) (hb : d237247 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29594, d237247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29594, d237247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29595 q = 1) (hb : d237248 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d29595, d237248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29595, d237248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro67271 (p : Pattern) (ha : d237254 p = 1) (hb : d267040 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237235 q = 1) (hb : d267023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237235, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67268 q ha hb
    | true =>
      simp only [d237235, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237236 q = 1) (hb : d267024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237236, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237236, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237237 q = 1) (hb : d267025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237237, d267025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237237, d267025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237238 q = 1) (hb : d267026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237238, d267026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237238, d267026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237245 q = 1) (hb : d267035 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237245, d267035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237245, d267035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d29596 q = 1) (hb : d237249 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29596, d237249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67270 q ha hb
    | true =>
      simp only [d29596, d237249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29597 q = 1) (hb : d237250 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29597, d237250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29597, d237250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29598 q = 1) (hb : d237251 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29598, d237251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29598, d237251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d29599 q = 1) (hb : d237252 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29599, d237252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29599, d237252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d29600 q = 1) (hb : d237253 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29600, d237253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29600, d237253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d237254 q = 1) (hb : d267040 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237254, d267040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237254, d267040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro67272 (p : Pattern) (ha : d237261 p = 1) (hb : d267047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237242 q = 1) (hb : d267037 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237242, d267037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67266 q ha hb
    | true =>
      simp only [d237242, d267037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67269 q ha hb
  have h2 (q : Pattern) (ha : d237243 q = 1) (hb : d267038 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237243, d267038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237243, d267038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237244 q = 1) (hb : d267039 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237244, d267039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237244, d267039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237255 q = 1) (hb : d267041 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237255, d267041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67269 q ha hb
    | true =>
      simp only [d237255, d267041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67271 q ha hb
  have h5 (q : Pattern) (ha : d237256 q = 1) (hb : d267042 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237256, d267042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237256, d267042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237257 q = 1) (hb : d267043 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237257, d267043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237257, d267043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237258 q = 1) (hb : d267044 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237258, d267044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237258, d267044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237259 q = 1) (hb : d267045 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237259, d267045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237259, d267045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237260 q = 1) (hb : d267046 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237260, d267046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237260, d267046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237261 q = 1) (hb : d267047 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237261, d267047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237261, d267047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro67273 (p : Pattern) (ha : d237265 p = 1) (hb : d267051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237255 q = 1) (hb : d267041 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237255, d267041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67269 q ha hb
    | true =>
      simp only [d237255, d267041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67271 q ha hb
  have h2 (q : Pattern) (ha : d237256 q = 1) (hb : d267042 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237256, d267042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237256, d267042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237257 q = 1) (hb : d267043 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237257, d267043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237257, d267043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237259 q = 1) (hb : d267045 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237259, d267045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237259, d267045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237264 q = 1) (hb : d267050 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237264, d267050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237264, d267050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237265 q = 1) (hb : d267051 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237265, d267051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237265, d267051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67274 (p : Pattern) (ha : d237271 p = 1) (hb : d267057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237262 q = 1) (hb : d267048 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237262, d267048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67272 q ha hb
    | true =>
      simp only [d237262, d267048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237263 q = 1) (hb : d267049 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237263, d267049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237263, d267049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237266 q = 1) (hb : d267052 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67273 q ha hb
    | true =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237267 q = 1) (hb : d267053 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237268 q = 1) (hb : d267054 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237268, d267054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237268, d267054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237269 q = 1) (hb : d267055 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237269, d267055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237269, d267055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237270 q = 1) (hb : d267056 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237270, d267056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237270, d267056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237271 q = 1) (hb : d267057 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237271, d267057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237271, d267057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67275 (p : Pattern) (ha : d237275 p = 1) (hb : d267061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237266 q = 1) (hb : d267052 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67273 q ha hb
    | true =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237267 q = 1) (hb : d267053 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237272 q = 1) (hb : d267058 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237272, d267058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237272, d267058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237273 q = 1) (hb : d267059 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237273, d267059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237273, d267059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237274 q = 1) (hb : d267060 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237274, d267060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237274, d267060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237275 q = 1) (hb : d267061 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237275, d267061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237275, d267061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67276 (p : Pattern) (ha : d237281 p = 1) (hb : d267067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237276 q = 1) (hb : d267062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237276, d267062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67274 q ha hb
    | true =>
      simp only [d237276, d267062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67275 q ha hb
  have h2 (q : Pattern) (ha : d237277 q = 1) (hb : d267063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237277, d267063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237277, d267063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237278 q = 1) (hb : d267064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237278, d267064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237278, d267064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237279 q = 1) (hb : d267065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237279, d267065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237279, d267065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237280 q = 1) (hb : d267066 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237280, d267066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237280, d267066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237281 q = 1) (hb : d267067 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237281, d267067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237281, d267067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67277 (p : Pattern) (ha : d237284 p = 1) (hb : d267070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237262 q = 1) (hb : d267048 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237262, d267048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67272 q ha hb
    | true =>
      simp only [d237262, d267048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237263 q = 1) (hb : d267049 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237263, d267049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237263, d267049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237266 q = 1) (hb : d267052 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67273 q ha hb
    | true =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237267 q = 1) (hb : d267053 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237268 q = 1) (hb : d267054 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237268, d267054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237268, d267054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237269 q = 1) (hb : d267055 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237269, d267055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237269, d267055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237270 q = 1) (hb : d267056 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237270, d267056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237270, d267056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237284 q = 1) (hb : d267070 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237284, d267070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237284, d267070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro67278 (p : Pattern) (ha : d237285 p = 1) (hb : d267071 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237266 q = 1) (hb : d267052 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67273 q ha hb
    | true =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237267 q = 1) (hb : d267053 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237272 q = 1) (hb : d267058 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237272, d267058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237272, d267058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237273 q = 1) (hb : d267059 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237273, d267059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237273, d267059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237274 q = 1) (hb : d267060 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237274, d267060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237274, d267060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237285 q = 1) (hb : d267071 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237285, d267071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237285, d267071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67279 (p : Pattern) (ha : d237291 p = 1) (hb : d267077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237276 q = 1) (hb : d267062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237276, d267062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67274 q ha hb
    | true =>
      simp only [d237276, d267062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67275 q ha hb
  have h2 (q : Pattern) (ha : d237277 q = 1) (hb : d267063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237277, d267063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237277, d267063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237278 q = 1) (hb : d267064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237278, d267064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237278, d267064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237279 q = 1) (hb : d267065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237279, d267065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237279, d267065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237280 q = 1) (hb : d267066 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237280, d267066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237280, d267066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237286 q = 1) (hb : d267072 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237286, d267072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67277 q ha hb
    | true =>
      simp only [d237286, d267072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67278 q ha hb
  have h7 (q : Pattern) (ha : d237287 q = 1) (hb : d267073 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237287, d267073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237287, d267073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237288 q = 1) (hb : d267074 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237288, d267074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237288, d267074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237289 q = 1) (hb : d267075 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237289, d267075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237289, d267075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237290 q = 1) (hb : d267076 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237290, d267076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237290, d267076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237291 q = 1) (hb : d267077 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237291, d267077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237291, d267077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro67280 (p : Pattern) (ha : d237296 p = 1) (hb : d267082 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237262 q = 1) (hb : d267048 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237262, d267048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67272 q ha hb
    | true =>
      simp only [d237262, d267048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237263 q = 1) (hb : d267049 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237263, d267049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237263, d267049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237266 q = 1) (hb : d267052 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67273 q ha hb
    | true =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237267 q = 1) (hb : d267053 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237268 q = 1) (hb : d267054 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237268, d267054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237268, d267054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237269 q = 1) (hb : d267055 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237269, d267055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237269, d267055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237295 q = 1) (hb : d267081 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237295, d267081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237295, d267081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237296 q = 1) (hb : d267082 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237296, d267082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237296, d267082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67281 (p : Pattern) (ha : d237298 p = 1) (hb : d267084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237266 q = 1) (hb : d267052 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67273 q ha hb
    | true =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237267 q = 1) (hb : d267053 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237272 q = 1) (hb : d267058 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237272, d267058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237272, d267058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237273 q = 1) (hb : d267059 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237273, d267059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237273, d267059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237297 q = 1) (hb : d267083 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237297, d267083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237297, d267083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237298 q = 1) (hb : d267084 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237298, d267084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237298, d267084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67282 (p : Pattern) (ha : d237305 p = 1) (hb : d267091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237262 q = 1) (hb : d267048 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237262, d267048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67272 q ha hb
    | true =>
      simp only [d237262, d267048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237263 q = 1) (hb : d267049 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237263, d267049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237263, d267049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237266 q = 1) (hb : d267052 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67273 q ha hb
    | true =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237267 q = 1) (hb : d267053 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237268 q = 1) (hb : d267054 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237268, d267054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237268, d267054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237303 q = 1) (hb : d267089 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237303, d267089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237303, d267089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237304 q = 1) (hb : d267090 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237304, d267090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237304, d267090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237305 q = 1) (hb : d267091 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237305, d267091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237305, d267091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67283 (p : Pattern) (ha : d237308 p = 1) (hb : d267094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237266 q = 1) (hb : d267052 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67273 q ha hb
    | true =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237267 q = 1) (hb : d267053 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237272 q = 1) (hb : d267058 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237272, d267058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237272, d267058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237306 q = 1) (hb : d267092 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237306, d267092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237306, d267092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237307 q = 1) (hb : d267093 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237307, d267093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237307, d267093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237308 q = 1) (hb : d267094 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237308, d267094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237308, d267094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67284 (p : Pattern) (ha : d26652 p = 1) (hb : d237312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d209033 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1200 q = 1) (hb : d52781 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro172 q ha hb
    | true =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1201 q = 1) (hb : d52782 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d237181 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10042 q = 1) (hb : d237182 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10042, d237182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10042, d237182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10043 q = 1) (hb : d237183 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10043, d237183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10043, d237183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10044 q = 1) (hb : d237184 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10044, d237184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10044, d237184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d26652 q = 1) (hb : d237312 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26652, d237312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26652, d237312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67285 (p : Pattern) (ha : d237317 p = 1) (hb : d266999 p = 1) : d0 p = 1 := by
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
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d237181 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10042 q = 1) (hb : d237182 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10042, d237182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10042, d237182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10043 q = 1) (hb : d237183 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10043, d237183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10043, d237183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10044 q = 1) (hb : d237184 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10044, d237184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10044, d237184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29527 q = 1) (hb : d237180 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d29527, d237180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d29527, d237180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29528 q = 1) (hb : d237181 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d29528, d237181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29528, d237181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d237186 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d237187 q = 1) (hb : d266996 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d237187, d266996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d237187, d266996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d237208 q = 1) (hb : d266997 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d237208, d266997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237208, d266997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237209 q = 1) (hb : d266998 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d237209, d266998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237209, d266998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237317 q = 1) (hb : d266999 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d237317, d266999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d237317, d266999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro67286 (p : Pattern) (ha : d237324 p = 1) (hb : d267100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26653 q = 1) (hb : d237313 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26653, d237313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67284 q ha hb
    | true =>
      simp only [d26653, d237313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26654 q = 1) (hb : d237314 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26654, d237314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26654, d237314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26655 q = 1) (hb : d237315 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26655, d237315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26655, d237315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26656 q = 1) (hb : d237316 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26656, d237316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26656, d237316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d237318 q = 1) (hb : d267000 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237318, d267000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67285 q ha hb
    | true =>
      simp only [d237318, d267000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237319 q = 1) (hb : d267001 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237319, d267001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237319, d267001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237320 q = 1) (hb : d267002 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237320, d267002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237320, d267002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237321 q = 1) (hb : d267003 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237321, d267003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237321, d267003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237322 q = 1) (hb : d267098 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237322, d267098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d237322, d267098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237211 q = 1) (hb : d267016 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237211, d267016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67264 q ha hb
    | true =>
      simp only [d237211, d267016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237212 q = 1) (hb : d267017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237212, d267017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237212, d267017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237213 q = 1) (hb : d267018 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237213, d267018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237213, d267018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237214 q = 1) (hb : d267019 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237214, d267019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237214, d267019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d237323 q = 1) (hb : d267099 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237323, d267099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237323, d267099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d237324 q = 1) (hb : d267100 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237324, d267100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237324, d267100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro67287 (p : Pattern) (ha : d237328 p = 1) (hb : d267104 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237211 q = 1) (hb : d267016 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237211, d267016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67264 q ha hb
    | true =>
      simp only [d237211, d267016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237212 q = 1) (hb : d267017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237212, d267017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237212, d267017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237213 q = 1) (hb : d267018 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237213, d267018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237213, d267018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237214 q = 1) (hb : d267019 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237214, d267019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237214, d267019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237221 q = 1) (hb : d267023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237221, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67265 q ha hb
    | true =>
      simp only [d237221, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237222 q = 1) (hb : d267024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237222, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237222, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237223 q = 1) (hb : d267025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237223, d267025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237223, d267025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237224 q = 1) (hb : d267026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237224, d267026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237224, d267026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237225 q = 1) (hb : d267027 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237225, d267027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237225, d267027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237240 q = 1) (hb : d267035 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237240, d267035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237240, d267035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237328 q = 1) (hb : d267104 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237328, d267104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237328, d267104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro67288 (p : Pattern) (ha : d237334 p = 1) (hb : d267110 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237325 q = 1) (hb : d267101 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237325, d267101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67286 q ha hb
    | true =>
      simp only [d237325, d267101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67266 q ha hb
  have h2 (q : Pattern) (ha : d237326 q = 1) (hb : d267102 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237326, d267102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237326, d267102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237327 q = 1) (hb : d267103 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237327, d267103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237327, d267103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237329 q = 1) (hb : d267105 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237329, d267105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67266 q ha hb
    | true =>
      simp only [d237329, d267105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67287 q ha hb
  have h5 (q : Pattern) (ha : d237330 q = 1) (hb : d267106 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237330, d267106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237330, d267106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237331 q = 1) (hb : d267107 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237331, d267107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237331, d267107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237332 q = 1) (hb : d267108 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237332, d267108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237332, d267108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237242 q = 1) (hb : d267037 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237242, d267037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67266 q ha hb
    | true =>
      simp only [d237242, d267037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67269 q ha hb
  have h9 (q : Pattern) (ha : d237243 q = 1) (hb : d267038 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237243, d267038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237243, d267038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237244 q = 1) (hb : d267039 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237244, d267039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237244, d267039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237255 q = 1) (hb : d267041 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237255, d267041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67269 q ha hb
    | true =>
      simp only [d237255, d267041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67271 q ha hb
  have h12 (q : Pattern) (ha : d237256 q = 1) (hb : d267042 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237256, d267042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237256, d267042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237257 q = 1) (hb : d267043 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237257, d267043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237257, d267043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237258 q = 1) (hb : d267044 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237258, d267044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237258, d267044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d237333 q = 1) (hb : d267109 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237333, d267109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237333, d267109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d237334 q = 1) (hb : d267110 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237334, d267110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237334, d267110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro67289 (p : Pattern) (ha : d237340 p = 1) (hb : d267116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237335 q = 1) (hb : d267111 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237335, d267111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67288 q ha hb
    | true =>
      simp only [d237335, d267111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237336 q = 1) (hb : d267112 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237336, d267112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237336, d267112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237262 q = 1) (hb : d267048 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237262, d267048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67272 q ha hb
    | true =>
      simp only [d237262, d267048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237263 q = 1) (hb : d267049 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237263, d267049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237263, d267049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237337 q = 1) (hb : d267113 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237337, d267113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237337, d267113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237338 q = 1) (hb : d267114 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237338, d267114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237338, d267114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237339 q = 1) (hb : d267115 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237339, d267115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237339, d267115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237340 q = 1) (hb : d267116 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237340, d267116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237340, d267116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67290 (p : Pattern) (ha : d237345 p = 1) (hb : d267119 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29532 q = 1) (hb : d237185 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d29532, d237185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d29532, d237185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29533 q = 1) (hb : d237186 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d29533, d237186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29533, d237186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d237199 q = 1) (hb : d267006 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d237199, d267006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d237199, d267006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d25765 q = 1) (hb : d52990 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25765, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62639 q ha hb
    | true =>
      simp only [d25765, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25766 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25766, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25766, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25767 q = 1) (hb : d101508 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25767, d101508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25767, d101508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d237215 q = 1) (hb : d267020 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d237215, d267020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237215, d267020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d237216 q = 1) (hb : d267021 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d237216, d267021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237216, d267021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d237217 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1578 q = 1) (hb : d53019 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d235519 q = 1) (hb : d237343 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d235519, d237343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d235519, d237343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d235520 q = 1) (hb : d237344 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d235520, d237344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d235520, d237344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d237345 q = 1) (hb : d267119 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d237345, d267119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237345, d267119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro67291 (p : Pattern) (ha : d237351 p = 1) (hb : d267125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237230 q = 1) (hb : d267030 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237230, d267030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67267 q ha hb
    | true =>
      simp only [d237230, d267030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237231 q = 1) (hb : d267031 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237231, d267031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237231, d267031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237232 q = 1) (hb : d267032 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237232, d267032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237232, d267032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237233 q = 1) (hb : d267033 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237233, d267033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237233, d267033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237235 q = 1) (hb : d267023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237235, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67268 q ha hb
    | true =>
      simp only [d237235, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237236 q = 1) (hb : d267024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237236, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237236, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237237 q = 1) (hb : d267025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237237, d267025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237237, d267025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237238 q = 1) (hb : d267026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237238, d267026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237238, d267026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237239 q = 1) (hb : d267034 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237239, d267034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237239, d267034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237346 q = 1) (hb : d267120 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237346, d267120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67290 q ha hb
    | true =>
      simp only [d237346, d267120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237347 q = 1) (hb : d267121 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237347, d267121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237347, d267121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237348 q = 1) (hb : d267122 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237348, d267122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237348, d267122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237349 q = 1) (hb : d267123 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237349, d267123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237349, d267123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d237350 q = 1) (hb : d267124 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237350, d267124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237350, d267124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d237351 q = 1) (hb : d267125 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237351, d267125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237351, d267125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro67292 (p : Pattern) (ha : d237352 p = 1) (hb : d267119 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29532 q = 1) (hb : d237185 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d29532, d237185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d29532, d237185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29533 q = 1) (hb : d237186 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d29533, d237186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29533, d237186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d237199 q = 1) (hb : d267006 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d237199, d267006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d237199, d267006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d25765 q = 1) (hb : d52990 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25765, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62639 q ha hb
    | true =>
      simp only [d25765, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25766 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25766, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25766, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d25767 q = 1) (hb : d53007 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25767, d53007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25767, d53007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237227 q = 1) (hb : d267020 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d237227, d267020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237227, d267020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d237228 q = 1) (hb : d267021 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d237228, d267021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237228, d267021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d237217 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d1578 q = 1) (hb : d53019 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1578, d53019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d235519 q = 1) (hb : d237343 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d235519, d237343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d235519, d237343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d235520 q = 1) (hb : d237344 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d235520, d237344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d235520, d237344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d237352 q = 1) (hb : d267119 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d237352, d267119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237352, d267119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro67293 (p : Pattern) (ha : d237358 p = 1) (hb : d267126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237353 q = 1) (hb : d267120 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237353, d267120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67292 q ha hb
    | true =>
      simp only [d237353, d267120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237354 q = 1) (hb : d267121 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237354, d267121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237354, d267121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237355 q = 1) (hb : d267122 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237355, d267122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237355, d267122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237356 q = 1) (hb : d267123 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237356, d267123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237356, d267123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237357 q = 1) (hb : d267124 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237357, d267124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237357, d267124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237358 q = 1) (hb : d267126 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237358, d267126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237358, d267126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67294 (p : Pattern) (ha : d237364 p = 1) (hb : d267132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237242 q = 1) (hb : d267037 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237242, d267037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67266 q ha hb
    | true =>
      simp only [d237242, d267037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67269 q ha hb
  have h2 (q : Pattern) (ha : d237243 q = 1) (hb : d267038 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237243, d267038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237243, d267038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237244 q = 1) (hb : d267039 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237244, d267039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237244, d267039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237255 q = 1) (hb : d267041 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237255, d267041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67269 q ha hb
    | true =>
      simp only [d237255, d267041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67271 q ha hb
  have h5 (q : Pattern) (ha : d237256 q = 1) (hb : d267042 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237256, d267042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237256, d267042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237257 q = 1) (hb : d267043 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237257, d267043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237257, d267043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237258 q = 1) (hb : d267044 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237258, d267044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237258, d267044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237359 q = 1) (hb : d267127 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237359, d267127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67291 q ha hb
    | true =>
      simp only [d237359, d267127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67293 q ha hb
  have h9 (q : Pattern) (ha : d237360 q = 1) (hb : d267128 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237360, d267128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237360, d267128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237361 q = 1) (hb : d267129 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237361, d267129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237361, d267129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237362 q = 1) (hb : d267130 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237362, d267130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237362, d267130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237363 q = 1) (hb : d267131 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237363, d267131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237363, d267131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237364 q = 1) (hb : d267132 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237364, d267132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237364, d267132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro67295 (p : Pattern) (ha : d237370 p = 1) (hb : d267138 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237365 q = 1) (hb : d267133 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237365, d267133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67294 q ha hb
    | true =>
      simp only [d237365, d267133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237366 q = 1) (hb : d267134 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237366, d267134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237366, d267134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237367 q = 1) (hb : d267135 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237367, d267135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237367, d267135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237368 q = 1) (hb : d267136 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237368, d267136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237368, d267136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237369 q = 1) (hb : d267137 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237369, d267137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237369, d267137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237370 q = 1) (hb : d267138 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237370, d267138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237370, d267138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67296 (p : Pattern) (ha : d237376 p = 1) (hb : d267144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237299 q = 1) (hb : d267085 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237299, d267085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67280 q ha hb
    | true =>
      simp only [d237299, d267085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67281 q ha hb
  have h2 (q : Pattern) (ha : d237300 q = 1) (hb : d267086 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237300, d267086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237300, d267086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237301 q = 1) (hb : d267087 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237301, d267087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237301, d267087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237302 q = 1) (hb : d267088 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237302, d267088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237302, d267088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237309 q = 1) (hb : d267095 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237309, d267095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67282 q ha hb
    | true =>
      simp only [d237309, d267095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67283 q ha hb
  have h6 (q : Pattern) (ha : d237310 q = 1) (hb : d267096 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237310, d267096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237310, d267096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237311 q = 1) (hb : d267097 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237311, d267097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237311, d267097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237341 q = 1) (hb : d267117 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237341, d267117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67289 q ha hb
    | true =>
      simp only [d237341, d267117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67274 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d237276 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d237342 q = 1) (hb : d267118 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237342, d267118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237342, d267118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d237371 q = 1) (hb : d267139 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237371, d267139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67295 q ha hb
    | true =>
      simp only [d237371, d267139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237372 q = 1) (hb : d267140 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237372, d267140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237372, d267140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237373 q = 1) (hb : d267141 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237373, d267141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237373, d267141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237374 q = 1) (hb : d267142 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237374, d267142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237374, d267142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d237375 q = 1) (hb : d267143 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237375, d267143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237375, d267143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d237376 q = 1) (hb : d267144 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237376, d267144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237376, d267144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro67297 (p : Pattern) (ha : d237377 p = 1) (hb : d267145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237262 q = 1) (hb : d267048 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237262, d267048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67272 q ha hb
    | true =>
      simp only [d237262, d267048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237263 q = 1) (hb : d267049 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237263, d267049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237263, d267049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237266 q = 1) (hb : d267052 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67273 q ha hb
    | true =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237267 q = 1) (hb : d267053 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237268 q = 1) (hb : d267054 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237268, d267054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237268, d267054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237269 q = 1) (hb : d267055 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237269, d267055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237269, d267055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237295 q = 1) (hb : d267081 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237295, d267081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237295, d267081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237377 q = 1) (hb : d267145 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237377, d267145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237377, d267145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro67298 (p : Pattern) (ha : d237378 p = 1) (hb : d267146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237266 q = 1) (hb : d267052 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67273 q ha hb
    | true =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237267 q = 1) (hb : d267053 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237272 q = 1) (hb : d267058 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237272, d267058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237272, d267058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237273 q = 1) (hb : d267059 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237273, d267059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237273, d267059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237297 q = 1) (hb : d267083 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237297, d267083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237297, d267083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237378 q = 1) (hb : d267146 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237378, d267146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237378, d267146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67299 (p : Pattern) (ha : d237383 p = 1) (hb : d267151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237262 q = 1) (hb : d267048 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237262, d267048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67272 q ha hb
    | true =>
      simp only [d237262, d267048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237263 q = 1) (hb : d267049 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237263, d267049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237263, d267049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237266 q = 1) (hb : d267052 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67273 q ha hb
    | true =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237267 q = 1) (hb : d267053 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237268 q = 1) (hb : d267054 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237268, d267054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237268, d267054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237303 q = 1) (hb : d267089 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237303, d267089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237303, d267089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237304 q = 1) (hb : d267090 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237304, d267090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237304, d267090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237383 q = 1) (hb : d267151 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237383, d267151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237383, d267151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro67300 (p : Pattern) (ha : d237384 p = 1) (hb : d267152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237266 q = 1) (hb : d267052 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67273 q ha hb
    | true =>
      simp only [d237266, d267052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237267 q = 1) (hb : d267053 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237267, d267053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237272 q = 1) (hb : d267058 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237272, d267058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237272, d267058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237306 q = 1) (hb : d267092 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237306, d267092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237306, d267092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237307 q = 1) (hb : d267093 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237307, d267093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237307, d267093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237384 q = 1) (hb : d267152 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237384, d267152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237384, d267152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67301 (p : Pattern) (ha : d237388 p = 1) (hb : d267156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237335 q = 1) (hb : d267111 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237335, d267111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67288 q ha hb
    | true =>
      simp only [d237335, d267111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237336 q = 1) (hb : d267112 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237336, d267112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237336, d267112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237262 q = 1) (hb : d267048 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237262, d267048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67272 q ha hb
    | true =>
      simp only [d237262, d267048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237263 q = 1) (hb : d267049 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237263, d267049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237263, d267049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237337 q = 1) (hb : d267113 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237337, d267113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237337, d267113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237338 q = 1) (hb : d267114 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237338, d267114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237338, d267114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237339 q = 1) (hb : d267115 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237339, d267115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237339, d267115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237388 q = 1) (hb : d267156 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237388, d267156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237388, d267156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro67302 (p : Pattern) (ha : d237391 p = 1) (hb : d267159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237365 q = 1) (hb : d267133 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237365, d267133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67294 q ha hb
    | true =>
      simp only [d237365, d267133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237366 q = 1) (hb : d267134 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237366, d267134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237366, d267134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237367 q = 1) (hb : d267135 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237367, d267135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237367, d267135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237368 q = 1) (hb : d267136 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237368, d267136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237368, d267136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237369 q = 1) (hb : d267137 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237369, d267137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237369, d267137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237391 q = 1) (hb : d267159 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237391, d267159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237391, d267159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67303 (p : Pattern) (ha : d237397 p = 1) (hb : d267165 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237299 q = 1) (hb : d267085 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237299, d267085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67280 q ha hb
    | true =>
      simp only [d237299, d267085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67281 q ha hb
  have h2 (q : Pattern) (ha : d237300 q = 1) (hb : d267086 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237300, d267086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237300, d267086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237301 q = 1) (hb : d267087 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237301, d267087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237301, d267087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237302 q = 1) (hb : d267088 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237302, d267088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237302, d267088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237309 q = 1) (hb : d267095 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237309, d267095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67282 q ha hb
    | true =>
      simp only [d237309, d267095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67283 q ha hb
  have h6 (q : Pattern) (ha : d237310 q = 1) (hb : d267096 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237310, d267096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237310, d267096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237311 q = 1) (hb : d267097 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237311, d267097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237311, d267097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237341 q = 1) (hb : d267117 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237341, d267117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67289 q ha hb
    | true =>
      simp only [d237341, d267117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67274 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d237276 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d237342 q = 1) (hb : d267118 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237342, d267118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237342, d267118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d237371 q = 1) (hb : d267139 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237371, d267139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67295 q ha hb
    | true =>
      simp only [d237371, d267139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237372 q = 1) (hb : d267140 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237372, d267140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237372, d267140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237373 q = 1) (hb : d267141 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237373, d267141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237373, d267141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237374 q = 1) (hb : d267142 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237374, d267142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237374, d267142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d237375 q = 1) (hb : d267143 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237375, d267143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237375, d267143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d237379 q = 1) (hb : d267147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237379, d267147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67297 q ha hb
    | true =>
      simp only [d237379, d267147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67298 q ha hb
  have h17 (q : Pattern) (ha : d237380 q = 1) (hb : d267148 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237380, d267148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237380, d267148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d237381 q = 1) (hb : d267149 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237381, d267149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d237381, d267149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d237382 q = 1) (hb : d267150 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237382, d267150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237382, d267150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d237385 q = 1) (hb : d267153 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237385, d267153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67299 q ha hb
    | true =>
      simp only [d237385, d267153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67300 q ha hb
  have h21 (q : Pattern) (ha : d237386 q = 1) (hb : d267154 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237386, d267154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237386, d267154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d237387 q = 1) (hb : d267155 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237387, d267155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d237387, d267155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d237389 q = 1) (hb : d267157 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237389, d267157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67301 q ha hb
    | true =>
      simp only [d237389, d267157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67277 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d237286 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d237390 q = 1) (hb : d267158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237390, d267158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d237390, d267158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d237392 q = 1) (hb : d267160 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237392, d267160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67302 q ha hb
    | true =>
      simp only [d237392, d267160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d237393 q = 1) (hb : d267161 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237393, d267161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d237393, d267161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d237394 q = 1) (hb : d267162 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237394, d267162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d237394, d267162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d237395 q = 1) (hb : d267163 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237395, d267163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d237395, d267163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d237396 q = 1) (hb : d267164 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237396, d267164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d237396, d267164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d237397 q = 1) (hb : d267165 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237397, d267165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237397, d267165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro67304 (p : Pattern) (ha : d237404 p = 1) (hb : d267172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237276 q = 1) (hb : d267062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237276, d267062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67274 q ha hb
    | true =>
      simp only [d237276, d267062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67275 q ha hb
  have h2 (q : Pattern) (ha : d237277 q = 1) (hb : d267063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237277, d267063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237277, d267063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237278 q = 1) (hb : d267064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237278, d267064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237278, d267064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237279 q = 1) (hb : d267065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237279, d267065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237279, d267065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237280 q = 1) (hb : d267066 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237280, d267066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237280, d267066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237399 q = 1) (hb : d267167 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237399, d267167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67275 q ha hb
    | true =>
      simp only [d237399, d267167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237400 q = 1) (hb : d267168 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237400, d267168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237400, d267168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237401 q = 1) (hb : d267169 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237401, d267169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237401, d267169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237402 q = 1) (hb : d267170 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237402, d267170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237402, d267170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237403 q = 1) (hb : d267171 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237403, d267171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237403, d267171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237404 q = 1) (hb : d267172 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237404, d267172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237404, d267172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro67305 (p : Pattern) (ha : d237410 p = 1) (hb : d267178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237399 q = 1) (hb : d267167 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237399, d267167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67275 q ha hb
    | true =>
      simp only [d237399, d267167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237400 q = 1) (hb : d267168 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237400, d267168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237400, d267168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237401 q = 1) (hb : d267169 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237401, d267169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237401, d267169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237402 q = 1) (hb : d267170 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237402, d267170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237402, d267170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237403 q = 1) (hb : d267171 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237403, d267171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237403, d267171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237405 q = 1) (hb : d267173 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237405, d267173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67278 q ha hb
    | true =>
      simp only [d237405, d267173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237406 q = 1) (hb : d267174 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237406, d267174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237406, d267174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237407 q = 1) (hb : d267175 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237407, d267175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237407, d267175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237408 q = 1) (hb : d267176 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237408, d267176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237408, d267176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237409 q = 1) (hb : d267177 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237409, d267177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237409, d267177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237410 q = 1) (hb : d267178 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237410, d267178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237410, d267178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro67306 (p : Pattern) (ha : d237417 p = 1) (hb : d267185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237389 q = 1) (hb : d267157 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237389, d267157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67301 q ha hb
    | true =>
      simp only [d237389, d267157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67277 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237286 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d237390 q = 1) (hb : d267158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237390, d267158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237390, d267158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d237392 q = 1) (hb : d267160 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237392, d267160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67302 q ha hb
    | true =>
      simp only [d237392, d267160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237393 q = 1) (hb : d267161 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237393, d267161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237393, d267161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237394 q = 1) (hb : d267162 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237394, d267162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237394, d267162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237415 q = 1) (hb : d267183 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237415, d267183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237415, d267183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237416 q = 1) (hb : d267184 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237416, d267184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237416, d267184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237417 q = 1) (hb : d267185 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237417, d267185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237417, d267185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro67307 (p : Pattern) (ha : d237419 p = 1) (hb : d267187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237405 q = 1) (hb : d267173 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237405, d267173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67278 q ha hb
    | true =>
      simp only [d237405, d267173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237406 q = 1) (hb : d267174 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237406, d267174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237406, d267174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237407 q = 1) (hb : d267175 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237407, d267175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237407, d267175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237408 q = 1) (hb : d267176 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237408, d267176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237408, d267176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237409 q = 1) (hb : d267177 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237409, d267177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237409, d267177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237419 q = 1) (hb : d267187 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237419, d267187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237419, d267187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67308 (p : Pattern) (ha : d237439 p = 1) (hb : d267203 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26834 q = 1) (hb : d237425 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26834, d237425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26834, d237425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67284 q ha hb
  have h2 (q : Pattern) (ha : d26653 q = 1) (hb : d237313 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26653, d237313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67284 q ha hb
    | true =>
      simp only [d26653, d237313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26835 q = 1) (hb : d237426 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26835, d237426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26835, d237426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26654 q = 1) (hb : d237314 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26654, d237314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26654, d237314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26836 q = 1) (hb : d237427 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26836, d237427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26836, d237427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26837 q = 1) (hb : d237428 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26837, d237428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26837, d237428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d237429 q = 1) (hb : d267193 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237429, d267193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237429, d267193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67285 q ha hb
  have h8 (q : Pattern) (ha : d237318 q = 1) (hb : d267000 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237318, d267000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67285 q ha hb
    | true =>
      simp only [d237318, d267000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237430 q = 1) (hb : d267194 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237430, d267194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237430, d267194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237319 q = 1) (hb : d267001 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237319, d267001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237319, d267001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237431 q = 1) (hb : d267195 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237431, d267195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237431, d267195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d237432 q = 1) (hb : d267196 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237432, d267196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237432, d267196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237433 q = 1) (hb : d267197 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237433, d267197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d237433, d267197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237434 q = 1) (hb : d267198 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237434, d267198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237434, d267198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67264 q ha hb
  have h15 (q : Pattern) (ha : d237211 q = 1) (hb : d267016 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237211, d267016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67264 q ha hb
    | true =>
      simp only [d237211, d267016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d237435 q = 1) (hb : d267199 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237435, d267199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d237435, d267199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237212 q = 1) (hb : d267017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237212, d267017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237212, d267017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d237436 q = 1) (hb : d267200 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237436, d267200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237436, d267200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d237437 q = 1) (hb : d267201 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237437, d267201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d237437, d267201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d237438 q = 1) (hb : d267202 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237438, d267202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237438, d267202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d237439 q = 1) (hb : d267203 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237439, d267203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237439, d267203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro67309 (p : Pattern) (ha : d237454 p = 1) (hb : d267214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237440 q = 1) (hb : d267193 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237440, d267193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237440, d267193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67262 q ha hb
  have h2 (q : Pattern) (ha : d237192 q = 1) (hb : d267000 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237192, d267000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67262 q ha hb
    | true =>
      simp only [d237192, d267000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237441 q = 1) (hb : d267194 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237441, d267194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237441, d267194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237193 q = 1) (hb : d267001 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237193, d267001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237193, d267001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237442 q = 1) (hb : d267195 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237442, d267195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237442, d267195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237443 q = 1) (hb : d267196 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237443, d267196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237443, d267196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237444 q = 1) (hb : d267204 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237444, d267204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237444, d267204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67263 q ha hb
  have h8 (q : Pattern) (ha : d237203 q = 1) (hb : d267010 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237203, d267010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67263 q ha hb
    | true =>
      simp only [d237203, d267010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237445 q = 1) (hb : d267205 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237445, d267205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237445, d267205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237204 q = 1) (hb : d267011 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237204, d267011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237204, d267011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237446 q = 1) (hb : d267206 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237446, d267206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237446, d267206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d237447 q = 1) (hb : d267207 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237447, d267207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237447, d267207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237448 q = 1) (hb : d267208 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237448, d267208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237448, d267208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237434 q = 1) (hb : d267198 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237434, d267198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237434, d267198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67264 q ha hb
  have h15 (q : Pattern) (ha : d237211 q = 1) (hb : d267016 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237211, d267016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67264 q ha hb
    | true =>
      simp only [d237211, d267016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d237435 q = 1) (hb : d267199 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237435, d267199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d237435, d267199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237212 q = 1) (hb : d267017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237212, d267017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237212, d267017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d237436 q = 1) (hb : d267200 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237436, d267200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237436, d267200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d237437 q = 1) (hb : d267201 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237437, d267201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d237437, d267201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d237449 q = 1) (hb : d267209 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237449, d267209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237449, d267209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67265 q ha hb
  have h21 (q : Pattern) (ha : d237221 q = 1) (hb : d267023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237221, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67265 q ha hb
    | true =>
      simp only [d237221, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d237450 q = 1) (hb : d267210 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237450, d267210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d237450, d267210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d237222 q = 1) (hb : d267024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237222, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d237222, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d237451 q = 1) (hb : d267211 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237451, d267211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d237451, d267211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d237452 q = 1) (hb : d267212 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237452, d267212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d237452, d267212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d237453 q = 1) (hb : d267213 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237453, d267213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d237453, d267213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d237454 q = 1) (hb : d267214 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237454, d267214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237454, d267214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro67310 (p : Pattern) (ha : d237459 p = 1) (hb : d267219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237434 q = 1) (hb : d267198 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237434, d267198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237434, d267198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67264 q ha hb
  have h2 (q : Pattern) (ha : d237211 q = 1) (hb : d267016 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237211, d267016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67264 q ha hb
    | true =>
      simp only [d237211, d267016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237435 q = 1) (hb : d267199 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237435, d267199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237435, d267199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237212 q = 1) (hb : d267017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237212, d267017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237212, d267017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237436 q = 1) (hb : d267200 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237436, d267200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237436, d267200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237437 q = 1) (hb : d267201 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237437, d267201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237437, d267201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237449 q = 1) (hb : d267209 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237449, d267209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237449, d267209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67265 q ha hb
  have h8 (q : Pattern) (ha : d237221 q = 1) (hb : d267023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237221, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67265 q ha hb
    | true =>
      simp only [d237221, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237450 q = 1) (hb : d267210 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237450, d267210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237450, d267210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237222 q = 1) (hb : d267024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237222, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237222, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237451 q = 1) (hb : d267211 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237451, d267211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237451, d267211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d237452 q = 1) (hb : d267212 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237452, d267212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237452, d267212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237453 q = 1) (hb : d267213 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237453, d267213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237453, d267213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237458 q = 1) (hb : d267218 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237458, d267218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237458, d267218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d237459 q = 1) (hb : d267219 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237459, d267219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237459, d267219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro67311 (p : Pattern) (ha : d237473 p = 1) (hb : d267229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237464 q = 1) (hb : d267224 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237464, d267224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237464, d267224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67267 q ha hb
  have h2 (q : Pattern) (ha : d237230 q = 1) (hb : d267030 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237230, d267030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67267 q ha hb
    | true =>
      simp only [d237230, d267030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237465 q = 1) (hb : d267225 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237465, d267225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237465, d267225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237231 q = 1) (hb : d267031 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237231, d267031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237231, d267031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237466 q = 1) (hb : d267226 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237466, d267226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237466, d267226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237467 q = 1) (hb : d267227 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237467, d267227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237467, d267227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237468 q = 1) (hb : d267209 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237468, d267209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237468, d267209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67268 q ha hb
  have h8 (q : Pattern) (ha : d237235 q = 1) (hb : d267023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237235, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67268 q ha hb
    | true =>
      simp only [d237235, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237469 q = 1) (hb : d267210 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237469, d267210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237469, d267210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237236 q = 1) (hb : d267024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237236, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237236, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237470 q = 1) (hb : d267211 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237470, d267211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237470, d267211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d237471 q = 1) (hb : d267212 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237471, d267212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237471, d267212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237472 q = 1) (hb : d267228 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237472, d267228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237472, d267228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237449 q = 1) (hb : d267209 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237449, d267209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237449, d267209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67265 q ha hb
  have h15 (q : Pattern) (ha : d237221 q = 1) (hb : d267023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237221, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67265 q ha hb
    | true =>
      simp only [d237221, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d237450 q = 1) (hb : d267210 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237450, d267210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d237450, d267210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237222 q = 1) (hb : d267024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237222, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237222, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d237451 q = 1) (hb : d267211 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237451, d267211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237451, d267211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d237452 q = 1) (hb : d267212 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237452, d267212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d237452, d267212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d237458 q = 1) (hb : d267218 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237458, d267218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d237458, d267218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d237473 q = 1) (hb : d267229 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237473, d267229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237473, d267229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro67312 (p : Pattern) (ha : d237483 p = 1) (hb : d267233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237468 q = 1) (hb : d267209 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237468, d267209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237468, d267209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67268 q ha hb
  have h2 (q : Pattern) (ha : d237235 q = 1) (hb : d267023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237235, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67268 q ha hb
    | true =>
      simp only [d237235, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237469 q = 1) (hb : d267210 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237469, d267210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237469, d267210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237236 q = 1) (hb : d267024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237236, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237236, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237470 q = 1) (hb : d267211 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237470, d267211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237470, d267211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237471 q = 1) (hb : d267212 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237471, d267212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237471, d267212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237477 q = 1) (hb : d267218 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237477, d267218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237477, d267218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d29925 q = 1) (hb : d237478 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29925, d237478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29925, d237478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67270 q ha hb
  have h9 (q : Pattern) (ha : d29596 q = 1) (hb : d237249 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29596, d237249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67270 q ha hb
    | true =>
      simp only [d29596, d237249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d29926 q = 1) (hb : d237479 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29926, d237479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29926, d237479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d29597 q = 1) (hb : d237250 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29597, d237250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29597, d237250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d29927 q = 1) (hb : d237480 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29927, d237480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29927, d237480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d29928 q = 1) (hb : d237481 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29928, d237481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d29928, d237481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d29929 q = 1) (hb : d237482 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29929, d237482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29929, d237482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d237483 q = 1) (hb : d267233 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237483, d267233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237483, d267233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro67313 (p : Pattern) (ha : d237489 p = 1) (hb : d267239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237455 q = 1) (hb : d267215 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237455, d267215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67308 q ha hb
    | true =>
      simp only [d237455, d267215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67309 q ha hb
  have h2 (q : Pattern) (ha : d237456 q = 1) (hb : d267216 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237456, d267216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237456, d267216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237457 q = 1) (hb : d267217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237457, d267217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237457, d267217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237460 q = 1) (hb : d267220 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237460, d267220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67309 q ha hb
    | true =>
      simp only [d237460, d267220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67310 q ha hb
  have h5 (q : Pattern) (ha : d237461 q = 1) (hb : d267221 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237461, d267221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237461, d267221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237462 q = 1) (hb : d267222 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237462, d267222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237462, d267222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237463 q = 1) (hb : d267223 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237463, d267223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237463, d267223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237474 q = 1) (hb : d267230 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237474, d267230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67309 q ha hb
    | true =>
      simp only [d237474, d267230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67311 q ha hb
  have h9 (q : Pattern) (ha : d237475 q = 1) (hb : d267231 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237475, d267231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237475, d267231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237476 q = 1) (hb : d267232 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237476, d267232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237476, d267232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237484 q = 1) (hb : d267234 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237484, d267234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67311 q ha hb
    | true =>
      simp only [d237484, d267234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67312 q ha hb
  have h12 (q : Pattern) (ha : d237485 q = 1) (hb : d267235 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237485, d267235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237485, d267235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237486 q = 1) (hb : d267236 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237486, d267236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237486, d267236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237487 q = 1) (hb : d267237 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237487, d267237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237487, d267237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d237488 q = 1) (hb : d267238 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237488, d267238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237488, d267238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d237489 q = 1) (hb : d267239 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237489, d267239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237489, d267239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro67314 (p : Pattern) (ha : d237494 p = 1) (hb : d267244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237474 q = 1) (hb : d267230 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237474, d267230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67309 q ha hb
    | true =>
      simp only [d237474, d267230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67311 q ha hb
  have h2 (q : Pattern) (ha : d237475 q = 1) (hb : d267231 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237475, d267231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237475, d267231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237476 q = 1) (hb : d267232 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237476, d267232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237476, d267232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237484 q = 1) (hb : d267234 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237484, d267234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67311 q ha hb
    | true =>
      simp only [d237484, d267234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67312 q ha hb
  have h5 (q : Pattern) (ha : d237485 q = 1) (hb : d267235 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237485, d267235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237485, d267235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237486 q = 1) (hb : d267236 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237486, d267236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237486, d267236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237487 q = 1) (hb : d267237 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237487, d267237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237487, d267237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237492 q = 1) (hb : d267242 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237492, d267242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237492, d267242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237493 q = 1) (hb : d267243 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237493, d267243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237493, d267243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237494 q = 1) (hb : d267244 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237494, d267244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237494, d267244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro67315 (p : Pattern) (ha : d237500 p = 1) (hb : d267250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237490 q = 1) (hb : d267240 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237490, d267240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67313 q ha hb
    | true =>
      simp only [d237490, d267240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237491 q = 1) (hb : d267241 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237491, d267241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237491, d267241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237495 q = 1) (hb : d267245 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237495, d267245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67314 q ha hb
    | true =>
      simp only [d237495, d267245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237496 q = 1) (hb : d267246 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237496, d267246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237496, d267246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237497 q = 1) (hb : d267247 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237497, d267247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237497, d267247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237498 q = 1) (hb : d267248 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237498, d267248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237498, d267248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237499 q = 1) (hb : d267249 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237499, d267249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237499, d267249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237500 q = 1) (hb : d267250 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237500, d267250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237500, d267250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro67316 (p : Pattern) (ha : d237502 p = 1) (hb : d267252 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237484 q = 1) (hb : d267234 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237484, d267234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67311 q ha hb
    | true =>
      simp only [d237484, d267234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67312 q ha hb
  have h2 (q : Pattern) (ha : d237485 q = 1) (hb : d267235 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237485, d267235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237485, d267235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237486 q = 1) (hb : d267236 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237486, d267236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237486, d267236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237492 q = 1) (hb : d267242 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237492, d267242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237492, d267242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237501 q = 1) (hb : d267251 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237501, d267251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237501, d267251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237502 q = 1) (hb : d267252 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237502, d267252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237502, d267252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67317 (p : Pattern) (ha : d237508 p = 1) (hb : d267258 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237495 q = 1) (hb : d267245 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237495, d267245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67314 q ha hb
    | true =>
      simp only [d237495, d267245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237496 q = 1) (hb : d267246 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237496, d267246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237496, d267246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237503 q = 1) (hb : d267253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237503, d267253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67316 q ha hb
    | true =>
      simp only [d237503, d267253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237504 q = 1) (hb : d267254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237504, d267254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237504, d267254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237505 q = 1) (hb : d267255 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237505, d267255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237505, d267255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237506 q = 1) (hb : d267256 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237506, d267256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237506, d267256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237507 q = 1) (hb : d267257 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237507, d267257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237507, d267257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237508 q = 1) (hb : d267258 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237508, d267258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237508, d267258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro67318 (p : Pattern) (ha : d237521 p = 1) (hb : d267266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237464 q = 1) (hb : d267224 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237464, d267224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237464, d267224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67267 q ha hb
  have h2 (q : Pattern) (ha : d237230 q = 1) (hb : d267030 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237230, d267030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67267 q ha hb
    | true =>
      simp only [d237230, d267030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237465 q = 1) (hb : d267225 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237465, d267225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237465, d267225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237231 q = 1) (hb : d267031 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237231, d267031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237231, d267031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237466 q = 1) (hb : d267226 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237466, d267226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237466, d267226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237467 q = 1) (hb : d267227 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237467, d267227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237467, d267227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237468 q = 1) (hb : d267209 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237468, d267209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237468, d267209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67268 q ha hb
  have h8 (q : Pattern) (ha : d237235 q = 1) (hb : d267023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237235, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67268 q ha hb
    | true =>
      simp only [d237235, d267023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237469 q = 1) (hb : d267210 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237469, d267210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237469, d267210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237236 q = 1) (hb : d267024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237236, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237236, d267024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237470 q = 1) (hb : d267211 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237470, d267211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237470, d267211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d237471 q = 1) (hb : d267212 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237471, d267212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237471, d267212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237472 q = 1) (hb : d267228 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237472, d267228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237472, d267228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237516 q = 1) (hb : d267261 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237516, d267261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237516, d267261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67290 q ha hb
  have h15 (q : Pattern) (ha : d237346 q = 1) (hb : d267120 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237346, d267120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67290 q ha hb
    | true =>
      simp only [d237346, d267120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d237517 q = 1) (hb : d267262 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237517, d267262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d237517, d267262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237347 q = 1) (hb : d267121 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237347, d267121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237347, d267121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d237518 q = 1) (hb : d267263 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237518, d267263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237518, d267263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d237519 q = 1) (hb : d267264 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237519, d267264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d237519, d267264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d237520 q = 1) (hb : d267265 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237520, d267265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d237520, d267265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d237521 q = 1) (hb : d267266 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237521, d267266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237521, d267266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro67319 (p : Pattern) (ha : d237527 p = 1) (hb : d267267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237522 q = 1) (hb : d267261 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237522, d267261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237522, d267261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67292 q ha hb
  have h2 (q : Pattern) (ha : d237353 q = 1) (hb : d267120 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237353, d267120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67292 q ha hb
    | true =>
      simp only [d237353, d267120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237523 q = 1) (hb : d267262 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237523, d267262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237523, d267262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237354 q = 1) (hb : d267121 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237354, d267121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237354, d267121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237524 q = 1) (hb : d267263 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237524, d267263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237524, d267263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237525 q = 1) (hb : d267264 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237525, d267264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237525, d267264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237526 q = 1) (hb : d267265 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237526, d267265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237526, d267265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237527 q = 1) (hb : d267267 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237527, d267267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237527, d267267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro67320 (p : Pattern) (ha : d237533 p = 1) (hb : d267273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237474 q = 1) (hb : d267230 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237474, d267230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67309 q ha hb
    | true =>
      simp only [d237474, d267230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67311 q ha hb
  have h2 (q : Pattern) (ha : d237475 q = 1) (hb : d267231 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237475, d267231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237475, d267231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237476 q = 1) (hb : d267232 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237476, d267232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237476, d267232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237484 q = 1) (hb : d267234 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237484, d267234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67311 q ha hb
    | true =>
      simp only [d237484, d267234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67312 q ha hb
  have h5 (q : Pattern) (ha : d237485 q = 1) (hb : d267235 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237485, d267235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237485, d267235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237486 q = 1) (hb : d267236 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237486, d267236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237486, d267236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237487 q = 1) (hb : d267237 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237487, d267237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237487, d267237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237528 q = 1) (hb : d267268 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237528, d267268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67318 q ha hb
    | true =>
      simp only [d237528, d267268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67319 q ha hb
  have h9 (q : Pattern) (ha : d237529 q = 1) (hb : d267269 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237529, d267269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237529, d267269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237530 q = 1) (hb : d267270 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237530, d267270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237530, d267270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237531 q = 1) (hb : d267271 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237531, d267271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237531, d267271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237532 q = 1) (hb : d267272 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237532, d267272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237532, d267272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237533 q = 1) (hb : d267273 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237533, d267273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237533, d267273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro67321 (p : Pattern) (ha : d237539 p = 1) (hb : d267279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237534 q = 1) (hb : d267274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237534, d267274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67320 q ha hb
    | true =>
      simp only [d237534, d267274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237535 q = 1) (hb : d267275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237535, d267275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237535, d267275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237536 q = 1) (hb : d267276 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237536, d267276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237536, d267276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237537 q = 1) (hb : d267277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237537, d267277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237537, d267277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237538 q = 1) (hb : d267278 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237538, d267278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237538, d267278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237539 q = 1) (hb : d267279 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237539, d267279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237539, d267279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67322 (p : Pattern) (ha : d237545 p = 1) (hb : d267285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237509 q = 1) (hb : d267259 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237509, d267259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67315 q ha hb
    | true =>
      simp only [d237509, d267259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67317 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237514 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d237515 q = 1) (hb : d267260 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237515, d267260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237515, d267260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d237540 q = 1) (hb : d267280 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237540, d267280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67321 q ha hb
    | true =>
      simp only [d237540, d267280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237541 q = 1) (hb : d267281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237541, d267281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237541, d267281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237542 q = 1) (hb : d267282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237542, d267282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237542, d267282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237543 q = 1) (hb : d267283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237543, d267283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237543, d267283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237544 q = 1) (hb : d267284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237544, d267284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237544, d267284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237545 q = 1) (hb : d267285 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237545, d267285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237545, d267285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro67323 (p : Pattern) (ha : d237513 p = 1) (hb : d267290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237503 q = 1) (hb : d267253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237503, d267253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67316 q ha hb
    | true =>
      simp only [d237503, d267253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237504 q = 1) (hb : d267254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237504, d267254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237504, d267254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237510 q = 1) (hb : d267287 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237510, d267287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237510, d267287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237511 q = 1) (hb : d267288 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237511, d267288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237511, d267288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237512 q = 1) (hb : d267289 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237512, d267289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237512, d267289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237513 q = 1) (hb : d267290 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237513, d267290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237513, d267290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67324 (p : Pattern) (ha : d237552 p = 1) (hb : d267296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237547 q = 1) (hb : d267291 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237547, d267291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67323 q ha hb
    | true =>
      simp only [d237547, d267291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237548 q = 1) (hb : d267292 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237548, d267292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237548, d267292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237549 q = 1) (hb : d267293 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237549, d267293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237549, d267293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237550 q = 1) (hb : d267294 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237550, d267294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237550, d267294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237551 q = 1) (hb : d267295 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237551, d267295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237551, d267295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237552 q = 1) (hb : d267296 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237552, d267296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237552, d267296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67325 (p : Pattern) (ha : d237558 p = 1) (hb : d267302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237282 q = 1) (hb : d267068 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237282, d267068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237282, d267068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67276 q ha hb
  have h2 (q : Pattern) (ha : d237283 q = 1) (hb : d267069 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237283, d267069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237283, d267069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237292 q = 1) (hb : d267078 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237292, d267078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67276 q ha hb
    | true =>
      simp only [d237292, d267078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67279 q ha hb
  have h4 (q : Pattern) (ha : d237293 q = 1) (hb : d267079 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237293, d267079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237293, d267079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237294 q = 1) (hb : d267080 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237294, d267080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237294, d267080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237398 q = 1) (hb : d267166 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237398, d267166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67296 q ha hb
    | true =>
      simp only [d237398, d267166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67303 q ha hb
  have h7 (q : Pattern) (ha : d237411 q = 1) (hb : d267179 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237411, d267179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67304 q ha hb
    | true =>
      simp only [d237411, d267179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67305 q ha hb
  have h8 (q : Pattern) (ha : d237412 q = 1) (hb : d267180 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237412, d267180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237412, d267180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237413 q = 1) (hb : d267181 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237413, d267181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237413, d267181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d237414 q = 1) (hb : d267182 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237414, d267182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237414, d267182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237418 q = 1) (hb : d267186 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237418, d267186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237418, d267186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67306 q ha hb
  have h12 (q : Pattern) (ha : d237420 q = 1) (hb : d267188 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237420, d267188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237420, d267188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67307 q ha hb
  have h13 (q : Pattern) (ha : d237421 q = 1) (hb : d267189 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237421, d267189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237421, d267189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237422 q = 1) (hb : d267190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237422, d267190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237422, d267190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d237423 q = 1) (hb : d267191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237423, d267191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d237423, d267191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d237424 q = 1) (hb : d267192 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237424, d267192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237424, d267192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237546 q = 1) (hb : d267286 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237546, d267286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237546, d267286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67322 q ha hb
  have h18 (q : Pattern) (ha : d237553 q = 1) (hb : d267297 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237553, d267297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237553, d267297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67324 q ha hb
  have h19 (q : Pattern) (ha : d237554 q = 1) (hb : d267298 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237554, d267298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d237554, d267298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d237555 q = 1) (hb : d267299 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237555, d267299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d237555, d267299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d237556 q = 1) (hb : d267300 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237556, d267300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d237556, d267300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d237557 q = 1) (hb : d267301 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237557, d267301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d237557, d267301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d237558 q = 1) (hb : d267302 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d237558, d267302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237558, d267302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro67326 (p : Pattern) (ha : d237564 p = 1) (hb : d267308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237559 q = 1) (hb : d267303 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d237559, d267303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237559, d267303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67325 q ha hb
  have h2 (q : Pattern) (ha : d237560 q = 1) (hb : d267304 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d237560, d267304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237560, d267304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237561 q = 1) (hb : d267305 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d237561, d267305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237561, d267305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237562 q = 1) (hb : d267306 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d237562, d267306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237562, d267306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237563 q = 1) (hb : d267307 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d237563, d267307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237563, d267307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237564 q = 1) (hb : d267308 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d237564, d267308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237564, d267308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67327 (p : Pattern) (ha : d237579 p = 1) (hb : d258185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d237573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30077 q = 1) (hb : d237569 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30077, d237569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d30077, d237569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30078 q = 1) (hb : d237570 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30078, d237570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30078, d237570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d237575 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237576 q = 1) (hb : d257870 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d237576, d257870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d237576, d257870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237577 q = 1) (hb : d258183 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d237577, d258183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237577, d258183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d237578 q = 1) (hb : d258184 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d237578, d258184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237578, d258184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d237579 q = 1) (hb : d258185 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d237579, d258185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237579, d258185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67328 (p : Pattern) (ha : d237589 p = 1) (hb : d267313 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30077 q = 1) (hb : d237569 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30077, d237569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d30077, d237569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30078 q = 1) (hb : d237570 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30078, d237570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30078, d237570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d237575 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d237576 q = 1) (hb : d257870 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d237576, d257870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d237576, d257870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d237577 q = 1) (hb : d258183 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d237577, d258183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237577, d258183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237578 q = 1) (hb : d258184 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d237578, d258184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237578, d258184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d30082 q = 1) (hb : d237574 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30083 q = 1) (hb : d237575 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d237585 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d30309 q = 1) (hb : d237586 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30309, d237586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30309, d237586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30310 q = 1) (hb : d237587 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30310, d237587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30310, d237587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30311 q = 1) (hb : d237588 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30311, d237588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30311, d237588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d237589 q = 1) (hb : d267313 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d237589, d267313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237589, d267313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro67329 (p : Pattern) (ha : d237598 p = 1) (hb : d267319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30082 q = 1) (hb : d237574 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30083 q = 1) (hb : d237575 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d237585 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30309 q = 1) (hb : d237586 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30309, d237586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30309, d237586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30310 q = 1) (hb : d237587 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30310, d237587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30310, d237587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30311 q = 1) (hb : d237588 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30311, d237588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30311, d237588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d237595 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10405 q = 1) (hb : d101726 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10405, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
    | true =>
      simp only [d10405, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10406 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10406, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
    | true =>
      simp only [d10406, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10407 q = 1) (hb : d101728 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10407, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10407, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10408 q = 1) (hb : d101729 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10408, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10408, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30132 q = 1) (hb : d237596 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30132, d237596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30132, d237596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30133 q = 1) (hb : d237597 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30133, d237597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30133, d237597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d237598 q = 1) (hb : d267319 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d237598, d267319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d237598, d267319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro67330 (p : Pattern) (ha : d237604 p = 1) (hb : d267325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237580 q = 1) (hb : d258186 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237580, d258186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67327 q ha hb
    | true =>
      simp only [d237580, d258186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237581 q = 1) (hb : d258187 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237581, d258187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237581, d258187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237582 q = 1) (hb : d258188 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237582, d258188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237582, d258188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237583 q = 1) (hb : d258189 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237583, d258189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237583, d258189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237590 q = 1) (hb : d267314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237590, d267314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67328 q ha hb
    | true =>
      simp only [d237590, d267314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237591 q = 1) (hb : d267315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237591, d267315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237591, d267315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237592 q = 1) (hb : d267316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237592, d267316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237592, d267316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237593 q = 1) (hb : d267317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237593, d267317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237593, d267317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237594 q = 1) (hb : d267318 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237594, d267318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237594, d267318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237599 q = 1) (hb : d267320 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237599, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67329 q ha hb
    | true =>
      simp only [d237599, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237600 q = 1) (hb : d267321 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237600, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237600, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237601 q = 1) (hb : d267322 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237601, d267322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237601, d267322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237602 q = 1) (hb : d267323 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237602, d267323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237602, d267323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d237603 q = 1) (hb : d267324 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237603, d267324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237603, d267324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d237604 q = 1) (hb : d267325 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237604, d267325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237604, d267325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro67331 (p : Pattern) (ha : d237607 p = 1) (hb : d267313 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30077 q = 1) (hb : d237569 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30077, d237569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d30077, d237569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30078 q = 1) (hb : d237570 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30078, d237570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30078, d237570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d237575 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d237576 q = 1) (hb : d257870 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d237576, d257870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d237576, d257870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d237577 q = 1) (hb : d258183 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d237577, d258183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237577, d258183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237578 q = 1) (hb : d258184 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d237578, d258184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237578, d258184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d30082 q = 1) (hb : d237574 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30083 q = 1) (hb : d237575 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d237585 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d30309 q = 1) (hb : d237586 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30309, d237586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30309, d237586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d237595 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d30310 q = 1) (hb : d237605 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30310, d237605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30310, d237605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30311 q = 1) (hb : d237606 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30311, d237606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30311, d237606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d237607 q = 1) (hb : d267313 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d237607, d267313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237607, d267313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro67332 (p : Pattern) (ha : d237612 p = 1) (hb : d267319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30082 q = 1) (hb : d237574 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30083 q = 1) (hb : d237575 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d237585 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30309 q = 1) (hb : d237586 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30309, d237586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30309, d237586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d237595 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30310 q = 1) (hb : d237605 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30310, d237605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30310, d237605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30311 q = 1) (hb : d237606 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30311, d237606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30311, d237606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10405 q = 1) (hb : d101726 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10405, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
    | true =>
      simp only [d10405, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10406 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10406, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
    | true =>
      simp only [d10406, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10407 q = 1) (hb : d101728 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10407, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10407, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10408 q = 1) (hb : d101729 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10408, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10408, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30132 q = 1) (hb : d237596 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30132, d237596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30132, d237596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30133 q = 1) (hb : d237597 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30133, d237597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30133, d237597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d237612 q = 1) (hb : d267319 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d237612, d267319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d237612, d267319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro67333 (p : Pattern) (ha : d237619 p = 1) (hb : d267327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237608 q = 1) (hb : d267314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237608, d267314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67331 q ha hb
    | true =>
      simp only [d237608, d267314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237609 q = 1) (hb : d267315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237609, d267315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237609, d267315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237610 q = 1) (hb : d267316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237610, d267316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237610, d267316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237611 q = 1) (hb : d267317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237611, d267317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237611, d267317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237613 q = 1) (hb : d267320 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237613, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67332 q ha hb
    | true =>
      simp only [d237613, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237614 q = 1) (hb : d267321 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237614, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237614, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237615 q = 1) (hb : d267322 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237615, d267322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237615, d267322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237616 q = 1) (hb : d267323 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237616, d267323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237616, d267323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237617 q = 1) (hb : d267324 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237617, d267324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237617, d267324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237599 q = 1) (hb : d267320 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237599, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67329 q ha hb
    | true =>
      simp only [d237599, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237600 q = 1) (hb : d267321 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237600, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237600, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237601 q = 1) (hb : d267322 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237601, d267322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237601, d267322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237602 q = 1) (hb : d267323 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237602, d267323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237602, d267323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d237618 q = 1) (hb : d267326 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237618, d267326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237618, d267326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d237619 q = 1) (hb : d267327 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237619, d267327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237619, d267327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro67334 (p : Pattern) (ha : d30134 p = 1) (hb : d237626 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10405 q = 1) (hb : d101726 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10405, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
    | true =>
      simp only [d10405, d101726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10406 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10406, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
    | true =>
      simp only [d10406, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10407 q = 1) (hb : d101728 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10407, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10407, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10408 q = 1) (hb : d101729 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10408, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10408, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30132 q = 1) (hb : d237624 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30132, d237624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30132, d237624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30133 q = 1) (hb : d237625 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30133, d237625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30133, d237625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30134 q = 1) (hb : d237626 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30134, d237626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30134, d237626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro67335 (p : Pattern) (ha : d237632 p = 1) (hb : d267331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237613 q = 1) (hb : d267320 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237613, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67332 q ha hb
    | true =>
      simp only [d237613, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237614 q = 1) (hb : d267321 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237614, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237614, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237615 q = 1) (hb : d267322 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237615, d267322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237615, d267322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237616 q = 1) (hb : d267323 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237616, d267323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237616, d267323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237623 q = 1) (hb : d267326 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237623, d267326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237623, d267326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d30135 q = 1) (hb : d237627 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30135, d237627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67334 q ha hb
    | true =>
      simp only [d30135, d237627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30136 q = 1) (hb : d237628 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30136, d237628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30136, d237628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30137 q = 1) (hb : d237629 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30137, d237629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30137, d237629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30138 q = 1) (hb : d237630 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30138, d237630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30138, d237630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30139 q = 1) (hb : d237631 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30139, d237631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30139, d237631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d237632 q = 1) (hb : d267331 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237632, d267331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237632, d267331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro67336 (p : Pattern) (ha : d237639 p = 1) (hb : d267338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237620 q = 1) (hb : d267328 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237620, d267328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67330 q ha hb
    | true =>
      simp only [d237620, d267328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67333 q ha hb
  have h2 (q : Pattern) (ha : d237621 q = 1) (hb : d267329 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237621, d267329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237621, d267329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237622 q = 1) (hb : d267330 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237622, d267330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237622, d267330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237633 q = 1) (hb : d267332 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237633, d267332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67333 q ha hb
    | true =>
      simp only [d237633, d267332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67335 q ha hb
  have h5 (q : Pattern) (ha : d237634 q = 1) (hb : d267333 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237634, d267333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237634, d267333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237635 q = 1) (hb : d267334 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237635, d267334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237635, d267334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237636 q = 1) (hb : d267335 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237636, d267335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237636, d267335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237637 q = 1) (hb : d267336 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237637, d267336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237637, d267336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237638 q = 1) (hb : d267337 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237638, d267337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237638, d267337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237639 q = 1) (hb : d267338 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237639, d267338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237639, d267338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro67337 (p : Pattern) (ha : d237643 p = 1) (hb : d267342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237633 q = 1) (hb : d267332 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237633, d267332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67333 q ha hb
    | true =>
      simp only [d237633, d267332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67335 q ha hb
  have h2 (q : Pattern) (ha : d237634 q = 1) (hb : d267333 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237634, d267333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237634, d267333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237635 q = 1) (hb : d267334 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237635, d267334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237635, d267334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237637 q = 1) (hb : d267336 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237637, d267336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237637, d267336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237642 q = 1) (hb : d267341 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237642, d267341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237642, d267341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237643 q = 1) (hb : d267342 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237643, d267342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237643, d267342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67338 (p : Pattern) (ha : d237649 p = 1) (hb : d267348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237640 q = 1) (hb : d267339 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237640, d267339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67336 q ha hb
    | true =>
      simp only [d237640, d267339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237641 q = 1) (hb : d267340 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237641, d267340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237641, d267340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237644 q = 1) (hb : d267343 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67337 q ha hb
    | true =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237645 q = 1) (hb : d267344 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237646 q = 1) (hb : d267345 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237646, d267345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237646, d267345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237647 q = 1) (hb : d267346 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237647, d267346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237647, d267346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237648 q = 1) (hb : d267347 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237648, d267347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237648, d267347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237649 q = 1) (hb : d267348 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237649, d267348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237649, d267348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67339 (p : Pattern) (ha : d237653 p = 1) (hb : d267352 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237644 q = 1) (hb : d267343 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67337 q ha hb
    | true =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237645 q = 1) (hb : d267344 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237650 q = 1) (hb : d267349 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237650, d267349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237650, d267349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237651 q = 1) (hb : d267350 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237651, d267350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237651, d267350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237652 q = 1) (hb : d267351 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237652, d267351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237652, d267351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237653 q = 1) (hb : d267352 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237653, d267352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237653, d267352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67340 (p : Pattern) (ha : d237659 p = 1) (hb : d267358 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237654 q = 1) (hb : d267353 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237654, d267353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67338 q ha hb
    | true =>
      simp only [d237654, d267353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67339 q ha hb
  have h2 (q : Pattern) (ha : d237655 q = 1) (hb : d267354 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237655, d267354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237655, d267354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237656 q = 1) (hb : d267355 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237656, d267355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237656, d267355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237657 q = 1) (hb : d267356 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237657, d267356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237657, d267356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237658 q = 1) (hb : d267357 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237658, d267357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237658, d267357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237659 q = 1) (hb : d267358 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237659, d267358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237659, d267358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67341 (p : Pattern) (ha : d237662 p = 1) (hb : d267361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237640 q = 1) (hb : d267339 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237640, d267339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67336 q ha hb
    | true =>
      simp only [d237640, d267339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237641 q = 1) (hb : d267340 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237641, d267340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237641, d267340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237644 q = 1) (hb : d267343 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67337 q ha hb
    | true =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237645 q = 1) (hb : d267344 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237646 q = 1) (hb : d267345 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237646, d267345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237646, d267345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237647 q = 1) (hb : d267346 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237647, d267346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237647, d267346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237648 q = 1) (hb : d267347 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237648, d267347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237648, d267347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237662 q = 1) (hb : d267361 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237662, d267361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237662, d267361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro67342 (p : Pattern) (ha : d237663 p = 1) (hb : d267362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237644 q = 1) (hb : d267343 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67337 q ha hb
    | true =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237645 q = 1) (hb : d267344 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237650 q = 1) (hb : d267349 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237650, d267349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237650, d267349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237651 q = 1) (hb : d267350 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237651, d267350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237651, d267350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237652 q = 1) (hb : d267351 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237652, d267351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237652, d267351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237663 q = 1) (hb : d267362 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237663, d267362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237663, d267362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67343 (p : Pattern) (ha : d237669 p = 1) (hb : d267368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237654 q = 1) (hb : d267353 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237654, d267353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67338 q ha hb
    | true =>
      simp only [d237654, d267353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67339 q ha hb
  have h2 (q : Pattern) (ha : d237655 q = 1) (hb : d267354 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237655, d267354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237655, d267354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237656 q = 1) (hb : d267355 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237656, d267355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237656, d267355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237657 q = 1) (hb : d267356 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237657, d267356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237657, d267356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237658 q = 1) (hb : d267357 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237658, d267357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237658, d267357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237664 q = 1) (hb : d267363 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237664, d267363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67341 q ha hb
    | true =>
      simp only [d237664, d267363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67342 q ha hb
  have h7 (q : Pattern) (ha : d237665 q = 1) (hb : d267364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237665, d267364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237665, d267364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237666 q = 1) (hb : d267365 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237666, d267365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237666, d267365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237667 q = 1) (hb : d267366 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237667, d267366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237667, d267366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237668 q = 1) (hb : d267367 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237668, d267367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237668, d267367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237669 q = 1) (hb : d267368 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237669, d267368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237669, d267368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro67344 (p : Pattern) (ha : d237674 p = 1) (hb : d267373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237640 q = 1) (hb : d267339 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237640, d267339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67336 q ha hb
    | true =>
      simp only [d237640, d267339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237641 q = 1) (hb : d267340 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237641, d267340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237641, d267340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237644 q = 1) (hb : d267343 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67337 q ha hb
    | true =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237645 q = 1) (hb : d267344 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237646 q = 1) (hb : d267345 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237646, d267345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237646, d267345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237647 q = 1) (hb : d267346 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237647, d267346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237647, d267346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237673 q = 1) (hb : d267372 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237673, d267372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237673, d267372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237674 q = 1) (hb : d267373 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237674, d267373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237674, d267373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67345 (p : Pattern) (ha : d237676 p = 1) (hb : d267375 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237644 q = 1) (hb : d267343 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67337 q ha hb
    | true =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237645 q = 1) (hb : d267344 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237650 q = 1) (hb : d267349 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237650, d267349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237650, d267349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237651 q = 1) (hb : d267350 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237651, d267350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237651, d267350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237675 q = 1) (hb : d267374 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237675, d267374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237675, d267374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237676 q = 1) (hb : d267375 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237676, d267375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237676, d267375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67346 (p : Pattern) (ha : d237683 p = 1) (hb : d267382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237640 q = 1) (hb : d267339 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237640, d267339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67336 q ha hb
    | true =>
      simp only [d237640, d267339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237641 q = 1) (hb : d267340 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237641, d267340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237641, d267340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237644 q = 1) (hb : d267343 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67337 q ha hb
    | true =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237645 q = 1) (hb : d267344 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237646 q = 1) (hb : d267345 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237646, d267345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237646, d267345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237681 q = 1) (hb : d267380 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237681, d267380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237681, d267380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237682 q = 1) (hb : d267381 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237682, d267381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237682, d267381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237683 q = 1) (hb : d267382 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237683, d267382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237683, d267382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67347 (p : Pattern) (ha : d237686 p = 1) (hb : d267385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237644 q = 1) (hb : d267343 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67337 q ha hb
    | true =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237645 q = 1) (hb : d267344 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237650 q = 1) (hb : d267349 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237650, d267349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237650, d267349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237684 q = 1) (hb : d267383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237684, d267383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237684, d267383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237685 q = 1) (hb : d267384 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237685, d267384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237685, d267384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237686 q = 1) (hb : d267385 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237686, d267385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237686, d267385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67348 (p : Pattern) (ha : d237696 p = 1) (hb : d267389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d237694 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d237580 q = 1) (hb : d258186 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237580, d258186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67327 q ha hb
    | true =>
      simp only [d237580, d258186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d237581 q = 1) (hb : d258187 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237581, d258187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237581, d258187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d237582 q = 1) (hb : d258188 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237582, d258188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237582, d258188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237583 q = 1) (hb : d258189 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237583, d258189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237583, d258189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d237695 q = 1) (hb : d258476 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237695, d258476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237695, d258476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237590 q = 1) (hb : d267314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237590, d267314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67328 q ha hb
    | true =>
      simp only [d237590, d267314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d237591 q = 1) (hb : d267315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237591, d267315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237591, d267315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d237592 q = 1) (hb : d267316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237592, d267316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237592, d267316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237593 q = 1) (hb : d267317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237593, d267317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237593, d267317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d237594 q = 1) (hb : d267318 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237594, d267318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237594, d267318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d237696 q = 1) (hb : d267389 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237696, d267389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237696, d267389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro67349 (p : Pattern) (ha : d237700 p = 1) (hb : d267327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237590 q = 1) (hb : d267314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237590, d267314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67328 q ha hb
    | true =>
      simp only [d237590, d267314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237591 q = 1) (hb : d267315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237591, d267315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237591, d267315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237592 q = 1) (hb : d267316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237592, d267316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237592, d267316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237593 q = 1) (hb : d267317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237593, d267317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237593, d267317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237599 q = 1) (hb : d267320 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237599, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67329 q ha hb
    | true =>
      simp only [d237599, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237600 q = 1) (hb : d267321 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237600, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237600, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237601 q = 1) (hb : d267322 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237601, d267322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237601, d267322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237602 q = 1) (hb : d267323 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237602, d267323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237602, d267323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237603 q = 1) (hb : d267324 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237603, d267324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237603, d267324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237618 q = 1) (hb : d267326 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237618, d267326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237618, d267326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237700 q = 1) (hb : d267327 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237700, d267327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237700, d267327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro67350 (p : Pattern) (ha : d237706 p = 1) (hb : d267395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237697 q = 1) (hb : d267390 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237697, d267390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67348 q ha hb
    | true =>
      simp only [d237697, d267390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67330 q ha hb
  have h2 (q : Pattern) (ha : d237698 q = 1) (hb : d267391 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237698, d267391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237698, d267391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237699 q = 1) (hb : d267392 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237699, d267392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237699, d267392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237701 q = 1) (hb : d267328 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237701, d267328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67330 q ha hb
    | true =>
      simp only [d237701, d267328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67349 q ha hb
  have h5 (q : Pattern) (ha : d237702 q = 1) (hb : d267329 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237702, d267329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237702, d267329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237703 q = 1) (hb : d267330 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237703, d267330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237703, d267330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237704 q = 1) (hb : d267393 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237704, d267393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237704, d267393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237620 q = 1) (hb : d267328 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237620, d267328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67330 q ha hb
    | true =>
      simp only [d237620, d267328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67333 q ha hb
  have h9 (q : Pattern) (ha : d237621 q = 1) (hb : d267329 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237621, d267329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237621, d267329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237622 q = 1) (hb : d267330 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237622, d267330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237622, d267330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237633 q = 1) (hb : d267332 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237633, d267332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67333 q ha hb
    | true =>
      simp only [d237633, d267332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67335 q ha hb
  have h12 (q : Pattern) (ha : d237634 q = 1) (hb : d267333 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237634, d267333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237634, d267333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237635 q = 1) (hb : d267334 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237635, d267334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237635, d267334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237636 q = 1) (hb : d267335 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237636, d267335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237636, d267335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d237705 q = 1) (hb : d267394 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237705, d267394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237705, d267394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d237706 q = 1) (hb : d267395 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237706, d267395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237706, d267395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro67351 (p : Pattern) (ha : d237712 p = 1) (hb : d267401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237707 q = 1) (hb : d267396 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237707, d267396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67350 q ha hb
    | true =>
      simp only [d237707, d267396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237708 q = 1) (hb : d267397 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237708, d267397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237708, d267397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237640 q = 1) (hb : d267339 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237640, d267339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67336 q ha hb
    | true =>
      simp only [d237640, d267339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237641 q = 1) (hb : d267340 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237641, d267340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237641, d267340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237709 q = 1) (hb : d267398 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237709, d267398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237709, d267398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237710 q = 1) (hb : d267399 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237710, d267399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237710, d267399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237711 q = 1) (hb : d267400 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237711, d267400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237711, d267400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237712 q = 1) (hb : d267401 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237712, d267401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237712, d267401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67352 (p : Pattern) (ha : d237720 p = 1) (hb : d267404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30082 q = 1) (hb : d237574 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30083 q = 1) (hb : d237575 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30309 q = 1) (hb : d237715 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30309, d237715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30309, d237715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30310 q = 1) (hb : d237716 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30310, d237716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30310, d237716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30311 q = 1) (hb : d237717 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30311, d237717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30311, d237717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d237595 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2061 q = 1) (hb : d53340 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d235791 q = 1) (hb : d237718 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d235791, d237718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d235791, d237718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d235792 q = 1) (hb : d237719 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d235792, d237719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d235792, d237719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d237720 q = 1) (hb : d267404 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d237720, d267404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d237720, d267404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro67353 (p : Pattern) (ha : d237726 p = 1) (hb : d267410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237608 q = 1) (hb : d267314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237608, d267314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67331 q ha hb
    | true =>
      simp only [d237608, d267314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237609 q = 1) (hb : d267315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237609, d267315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237609, d267315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237610 q = 1) (hb : d267316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237610, d267316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237610, d267316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237611 q = 1) (hb : d267317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237611, d267317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237611, d267317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237613 q = 1) (hb : d267320 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237613, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67332 q ha hb
    | true =>
      simp only [d237613, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237614 q = 1) (hb : d267321 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237614, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237614, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237615 q = 1) (hb : d267322 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237615, d267322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237615, d267322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237616 q = 1) (hb : d267323 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237616, d267323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237616, d267323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237617 q = 1) (hb : d267324 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237617, d267324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237617, d267324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237721 q = 1) (hb : d267405 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237721, d267405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67352 q ha hb
    | true =>
      simp only [d237721, d267405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237722 q = 1) (hb : d267406 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237722, d267406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237722, d267406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237723 q = 1) (hb : d267407 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237723, d267407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237723, d267407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237724 q = 1) (hb : d267408 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237724, d267408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237724, d267408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d237725 q = 1) (hb : d267409 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237725, d267409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237725, d267409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d237726 q = 1) (hb : d267410 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237726, d267410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237726, d267410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro67354 (p : Pattern) (ha : d237729 p = 1) (hb : d267404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30082 q = 1) (hb : d237574 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d30082, d237574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30083 q = 1) (hb : d237575 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30083, d237575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30309 q = 1) (hb : d237715 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30309, d237715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30309, d237715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d237595 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d30310 q = 1) (hb : d237727 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30310, d237727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30310, d237727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30311 q = 1) (hb : d237728 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30311, d237728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30311, d237728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2061 q = 1) (hb : d53340 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2061, d53340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d235791 q = 1) (hb : d237718 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d235791, d237718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235791, d237718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d235792 q = 1) (hb : d237719 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d235792, d237719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d235792, d237719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d237729 q = 1) (hb : d267404 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d237729, d267404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d237729, d267404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro67355 (p : Pattern) (ha : d237735 p = 1) (hb : d267411 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237730 q = 1) (hb : d267405 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237730, d267405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67354 q ha hb
    | true =>
      simp only [d237730, d267405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237731 q = 1) (hb : d267406 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237731, d267406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237731, d267406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237732 q = 1) (hb : d267407 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237732, d267407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237732, d267407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237733 q = 1) (hb : d267408 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237733, d267408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237733, d267408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237734 q = 1) (hb : d267409 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237734, d267409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237734, d267409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237735 q = 1) (hb : d267411 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237735, d267411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237735, d267411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67356 (p : Pattern) (ha : d237741 p = 1) (hb : d267417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237620 q = 1) (hb : d267328 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237620, d267328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67330 q ha hb
    | true =>
      simp only [d237620, d267328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67333 q ha hb
  have h2 (q : Pattern) (ha : d237621 q = 1) (hb : d267329 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237621, d267329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237621, d267329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237622 q = 1) (hb : d267330 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237622, d267330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237622, d267330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237633 q = 1) (hb : d267332 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237633, d267332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67333 q ha hb
    | true =>
      simp only [d237633, d267332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67335 q ha hb
  have h5 (q : Pattern) (ha : d237634 q = 1) (hb : d267333 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237634, d267333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237634, d267333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237635 q = 1) (hb : d267334 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237635, d267334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237635, d267334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237636 q = 1) (hb : d267335 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237636, d267335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237636, d267335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237736 q = 1) (hb : d267412 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237736, d267412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67353 q ha hb
    | true =>
      simp only [d237736, d267412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67355 q ha hb
  have h9 (q : Pattern) (ha : d237737 q = 1) (hb : d267413 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237737, d267413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237737, d267413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237738 q = 1) (hb : d267414 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237738, d267414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237738, d267414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237739 q = 1) (hb : d267415 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237739, d267415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237739, d267415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237740 q = 1) (hb : d267416 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237740, d267416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237740, d267416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237741 q = 1) (hb : d267417 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237741, d267417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237741, d267417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro67357 (p : Pattern) (ha : d237747 p = 1) (hb : d267423 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237742 q = 1) (hb : d267418 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237742, d267418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67356 q ha hb
    | true =>
      simp only [d237742, d267418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237743 q = 1) (hb : d267419 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237743, d267419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237743, d267419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237744 q = 1) (hb : d267420 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237744, d267420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237744, d267420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237745 q = 1) (hb : d267421 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237745, d267421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237745, d267421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237746 q = 1) (hb : d267422 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237746, d267422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237746, d267422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237747 q = 1) (hb : d267423 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237747, d267423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237747, d267423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67358 (p : Pattern) (ha : d237753 p = 1) (hb : d267429 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237677 q = 1) (hb : d267376 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237677, d267376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67344 q ha hb
    | true =>
      simp only [d237677, d267376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67345 q ha hb
  have h2 (q : Pattern) (ha : d237678 q = 1) (hb : d267377 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237678, d267377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237678, d267377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237679 q = 1) (hb : d267378 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237679, d267378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237679, d267378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237680 q = 1) (hb : d267379 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237680, d267379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237680, d267379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237687 q = 1) (hb : d267386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237687, d267386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67346 q ha hb
    | true =>
      simp only [d237687, d267386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67347 q ha hb
  have h6 (q : Pattern) (ha : d237688 q = 1) (hb : d267387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237688, d267387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237688, d267387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237689 q = 1) (hb : d267388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237689, d267388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237689, d267388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237713 q = 1) (hb : d267402 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237713, d267402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67351 q ha hb
    | true =>
      simp only [d237713, d267402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67338 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d237654 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d237714 q = 1) (hb : d267403 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237714, d267403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237714, d267403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d237748 q = 1) (hb : d267424 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237748, d267424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67357 q ha hb
    | true =>
      simp only [d237748, d267424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237749 q = 1) (hb : d267425 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237749, d267425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237749, d267425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237750 q = 1) (hb : d267426 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237750, d267426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237750, d267426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237751 q = 1) (hb : d267427 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237751, d267427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237751, d267427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d237752 q = 1) (hb : d267428 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237752, d267428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237752, d267428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d237753 q = 1) (hb : d267429 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237753, d267429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237753, d267429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro67359 (p : Pattern) (ha : d237754 p = 1) (hb : d267430 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237640 q = 1) (hb : d267339 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237640, d267339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67336 q ha hb
    | true =>
      simp only [d237640, d267339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237641 q = 1) (hb : d267340 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237641, d267340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237641, d267340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237644 q = 1) (hb : d267343 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67337 q ha hb
    | true =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237645 q = 1) (hb : d267344 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237646 q = 1) (hb : d267345 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237646, d267345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237646, d267345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237647 q = 1) (hb : d267346 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237647, d267346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237647, d267346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237673 q = 1) (hb : d267372 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237673, d267372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237673, d267372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237754 q = 1) (hb : d267430 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237754, d267430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237754, d267430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro67360 (p : Pattern) (ha : d237755 p = 1) (hb : d267431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237644 q = 1) (hb : d267343 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67337 q ha hb
    | true =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237645 q = 1) (hb : d267344 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237650 q = 1) (hb : d267349 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237650, d267349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237650, d267349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237651 q = 1) (hb : d267350 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237651, d267350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237651, d267350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237675 q = 1) (hb : d267374 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237675, d267374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237675, d267374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237755 q = 1) (hb : d267431 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237755, d267431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237755, d267431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67361 (p : Pattern) (ha : d237760 p = 1) (hb : d267436 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237640 q = 1) (hb : d267339 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237640, d267339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67336 q ha hb
    | true =>
      simp only [d237640, d267339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237641 q = 1) (hb : d267340 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237641, d267340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237641, d267340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237644 q = 1) (hb : d267343 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67337 q ha hb
    | true =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237645 q = 1) (hb : d267344 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237646 q = 1) (hb : d267345 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237646, d267345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237646, d267345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237681 q = 1) (hb : d267380 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237681, d267380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237681, d267380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237682 q = 1) (hb : d267381 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237682, d267381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237682, d267381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237760 q = 1) (hb : d267436 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237760, d267436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237760, d267436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro67362 (p : Pattern) (ha : d237761 p = 1) (hb : d267437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237644 q = 1) (hb : d267343 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67337 q ha hb
    | true =>
      simp only [d237644, d267343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237645 q = 1) (hb : d267344 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237645, d267344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237650 q = 1) (hb : d267349 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237650, d267349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237650, d267349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237684 q = 1) (hb : d267383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237684, d267383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237684, d267383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237685 q = 1) (hb : d267384 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237685, d267384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237685, d267384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237761 q = 1) (hb : d267437 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237761, d267437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237761, d267437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67363 (p : Pattern) (ha : d237765 p = 1) (hb : d267441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237707 q = 1) (hb : d267396 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237707, d267396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67350 q ha hb
    | true =>
      simp only [d237707, d267396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237708 q = 1) (hb : d267397 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237708, d267397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237708, d267397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237640 q = 1) (hb : d267339 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237640, d267339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67336 q ha hb
    | true =>
      simp only [d237640, d267339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237641 q = 1) (hb : d267340 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237641, d267340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237641, d267340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237709 q = 1) (hb : d267398 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237709, d267398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237709, d267398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237710 q = 1) (hb : d267399 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237710, d267399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237710, d267399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237711 q = 1) (hb : d267400 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237711, d267400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237711, d267400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237765 q = 1) (hb : d267441 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237765, d267441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237765, d267441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro67364 (p : Pattern) (ha : d237768 p = 1) (hb : d267444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237742 q = 1) (hb : d267418 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237742, d267418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67356 q ha hb
    | true =>
      simp only [d237742, d267418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237743 q = 1) (hb : d267419 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237743, d267419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237743, d267419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237744 q = 1) (hb : d267420 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237744, d267420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237744, d267420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237745 q = 1) (hb : d267421 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237745, d267421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237745, d267421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237746 q = 1) (hb : d267422 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237746, d267422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237746, d267422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237768 q = 1) (hb : d267444 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237768, d267444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237768, d267444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67365 (p : Pattern) (ha : d237774 p = 1) (hb : d267450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237677 q = 1) (hb : d267376 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237677, d267376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67344 q ha hb
    | true =>
      simp only [d237677, d267376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67345 q ha hb
  have h2 (q : Pattern) (ha : d237678 q = 1) (hb : d267377 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237678, d267377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237678, d267377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237679 q = 1) (hb : d267378 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237679, d267378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237679, d267378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237680 q = 1) (hb : d267379 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237680, d267379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237680, d267379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237687 q = 1) (hb : d267386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237687, d267386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67346 q ha hb
    | true =>
      simp only [d237687, d267386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67347 q ha hb
  have h6 (q : Pattern) (ha : d237688 q = 1) (hb : d267387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237688, d267387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237688, d267387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237689 q = 1) (hb : d267388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237689, d267388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237689, d267388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237713 q = 1) (hb : d267402 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237713, d267402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67351 q ha hb
    | true =>
      simp only [d237713, d267402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67338 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d237654 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d237714 q = 1) (hb : d267403 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237714, d267403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237714, d267403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d237748 q = 1) (hb : d267424 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237748, d267424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67357 q ha hb
    | true =>
      simp only [d237748, d267424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237749 q = 1) (hb : d267425 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237749, d267425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237749, d267425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237750 q = 1) (hb : d267426 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237750, d267426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237750, d267426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237751 q = 1) (hb : d267427 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237751, d267427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237751, d267427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d237752 q = 1) (hb : d267428 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237752, d267428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237752, d267428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d237756 q = 1) (hb : d267432 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237756, d267432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67359 q ha hb
    | true =>
      simp only [d237756, d267432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67360 q ha hb
  have h17 (q : Pattern) (ha : d237757 q = 1) (hb : d267433 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237757, d267433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237757, d267433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d237758 q = 1) (hb : d267434 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237758, d267434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d237758, d267434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d237759 q = 1) (hb : d267435 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237759, d267435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237759, d267435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d237762 q = 1) (hb : d267438 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237762, d267438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67361 q ha hb
    | true =>
      simp only [d237762, d267438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67362 q ha hb
  have h21 (q : Pattern) (ha : d237763 q = 1) (hb : d267439 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237763, d267439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237763, d267439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d237764 q = 1) (hb : d267440 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237764, d267440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d237764, d267440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d237766 q = 1) (hb : d267442 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237766, d267442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67363 q ha hb
    | true =>
      simp only [d237766, d267442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67341 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d237664 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d237767 q = 1) (hb : d267443 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237767, d267443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d237767, d267443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d237769 q = 1) (hb : d267445 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237769, d267445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67364 q ha hb
    | true =>
      simp only [d237769, d267445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d237770 q = 1) (hb : d267446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237770, d267446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d237770, d267446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d237771 q = 1) (hb : d267447 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237771, d267447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d237771, d267447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d237772 q = 1) (hb : d267448 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237772, d267448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d237772, d267448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d237773 q = 1) (hb : d267449 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237773, d267449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d237773, d267449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d237774 q = 1) (hb : d267450 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237774, d267450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237774, d267450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro67366 (p : Pattern) (ha : d237781 p = 1) (hb : d267457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237654 q = 1) (hb : d267353 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237654, d267353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67338 q ha hb
    | true =>
      simp only [d237654, d267353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67339 q ha hb
  have h2 (q : Pattern) (ha : d237655 q = 1) (hb : d267354 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237655, d267354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237655, d267354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237656 q = 1) (hb : d267355 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237656, d267355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237656, d267355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237657 q = 1) (hb : d267356 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237657, d267356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237657, d267356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237658 q = 1) (hb : d267357 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237658, d267357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237658, d267357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237776 q = 1) (hb : d267452 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237776, d267452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67339 q ha hb
    | true =>
      simp only [d237776, d267452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237777 q = 1) (hb : d267453 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237777, d267453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237777, d267453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237778 q = 1) (hb : d267454 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237778, d267454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237778, d267454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237779 q = 1) (hb : d267455 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237779, d267455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237779, d267455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237780 q = 1) (hb : d267456 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237780, d267456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237780, d267456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237781 q = 1) (hb : d267457 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237781, d267457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237781, d267457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro67367 (p : Pattern) (ha : d237787 p = 1) (hb : d267463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237776 q = 1) (hb : d267452 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237776, d267452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67339 q ha hb
    | true =>
      simp only [d237776, d267452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237777 q = 1) (hb : d267453 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237777, d267453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237777, d267453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237778 q = 1) (hb : d267454 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237778, d267454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237778, d267454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237779 q = 1) (hb : d267455 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237779, d267455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237779, d267455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237780 q = 1) (hb : d267456 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237780, d267456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237780, d267456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237782 q = 1) (hb : d267458 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237782, d267458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67342 q ha hb
    | true =>
      simp only [d237782, d267458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237783 q = 1) (hb : d267459 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237783, d267459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237783, d267459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237784 q = 1) (hb : d267460 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237784, d267460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237784, d267460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237785 q = 1) (hb : d267461 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237785, d267461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237785, d267461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237786 q = 1) (hb : d267462 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237786, d267462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237786, d267462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237787 q = 1) (hb : d267463 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237787, d267463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237787, d267463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro67368 (p : Pattern) (ha : d237794 p = 1) (hb : d267470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237766 q = 1) (hb : d267442 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237766, d267442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67363 q ha hb
    | true =>
      simp only [d237766, d267442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67341 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237664 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d237767 q = 1) (hb : d267443 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237767, d267443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237767, d267443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d237769 q = 1) (hb : d267445 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237769, d267445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67364 q ha hb
    | true =>
      simp only [d237769, d267445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237770 q = 1) (hb : d267446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237770, d267446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237770, d267446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237771 q = 1) (hb : d267447 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237771, d267447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237771, d267447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237792 q = 1) (hb : d267468 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237792, d267468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237792, d267468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237793 q = 1) (hb : d267469 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237793, d267469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237793, d267469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237794 q = 1) (hb : d267470 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237794, d267470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237794, d267470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro67369 (p : Pattern) (ha : d237796 p = 1) (hb : d267472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237782 q = 1) (hb : d267458 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237782, d267458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67342 q ha hb
    | true =>
      simp only [d237782, d267458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237783 q = 1) (hb : d267459 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237783, d267459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237783, d267459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237784 q = 1) (hb : d267460 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237784, d267460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237784, d267460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237785 q = 1) (hb : d267461 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237785, d267461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237785, d267461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237786 q = 1) (hb : d267462 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237786, d267462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237786, d267462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237796 q = 1) (hb : d267472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237796, d267472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237796, d267472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67370 (p : Pattern) (ha : d237816 p = 1) (hb : d267483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d237805 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d237806 q = 1) (hb : d258274 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237806, d258274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237806, d258274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67327 q ha hb
  have h3 (q : Pattern) (ha : d237580 q = 1) (hb : d258186 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237580, d258186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67327 q ha hb
    | true =>
      simp only [d237580, d258186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d237807 q = 1) (hb : d258275 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237807, d258275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237807, d258275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237581 q = 1) (hb : d258187 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237581, d258187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237581, d258187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d237808 q = 1) (hb : d258276 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237808, d258276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237808, d258276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237809 q = 1) (hb : d258277 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237809, d258277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237809, d258277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d237810 q = 1) (hb : d258554 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237810, d258554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237810, d258554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237811 q = 1) (hb : d267478 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237811, d267478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237811, d267478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67328 q ha hb
  have h10 (q : Pattern) (ha : d237590 q = 1) (hb : d267314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237590, d267314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67328 q ha hb
    | true =>
      simp only [d237590, d267314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h11 (q : Pattern) (ha : d237812 q = 1) (hb : d267479 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237812, d267479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237812, d267479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d237591 q = 1) (hb : d267315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237591, d267315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237591, d267315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d237813 q = 1) (hb : d267480 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237813, d267480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237813, d267480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237814 q = 1) (hb : d267481 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237814, d267481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237814, d267481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h15 (q : Pattern) (ha : d237815 q = 1) (hb : d267482 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237815, d267482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237815, d267482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d237816 q = 1) (hb : d267483 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237816, d267483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237816, d267483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro67371 (p : Pattern) (ha : d237822 p = 1) (hb : d267489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237806 q = 1) (hb : d258274 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237806, d258274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237806, d258274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67327 q ha hb
  have h2 (q : Pattern) (ha : d237580 q = 1) (hb : d258186 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237580, d258186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67327 q ha hb
    | true =>
      simp only [d237580, d258186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237807 q = 1) (hb : d258275 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237807, d258275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237807, d258275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237581 q = 1) (hb : d258187 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237581, d258187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237581, d258187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237808 q = 1) (hb : d258276 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237808, d258276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237808, d258276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237809 q = 1) (hb : d258277 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237809, d258277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237809, d258277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237811 q = 1) (hb : d267478 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237811, d267478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237811, d267478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67328 q ha hb
  have h8 (q : Pattern) (ha : d237590 q = 1) (hb : d267314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237590, d267314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67328 q ha hb
    | true =>
      simp only [d237590, d267314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237812 q = 1) (hb : d267479 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237812, d267479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237812, d267479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237591 q = 1) (hb : d267315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237591, d267315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237591, d267315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237813 q = 1) (hb : d267480 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237813, d267480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237813, d267480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d237814 q = 1) (hb : d267481 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237814, d267481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237814, d267481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237815 q = 1) (hb : d267482 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237815, d267482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237815, d267482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237817 q = 1) (hb : d267484 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237817, d267484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237817, d267484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67329 q ha hb
  have h15 (q : Pattern) (ha : d237599 q = 1) (hb : d267320 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237599, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67329 q ha hb
    | true =>
      simp only [d237599, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d237818 q = 1) (hb : d267485 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237818, d267485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d237818, d267485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237600 q = 1) (hb : d267321 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237600, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237600, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d237819 q = 1) (hb : d267486 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237819, d267486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237819, d267486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d237820 q = 1) (hb : d267487 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237820, d267487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d237820, d267487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d237821 q = 1) (hb : d267488 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237821, d267488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237821, d267488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d237822 q = 1) (hb : d267489 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237822, d267489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237822, d267489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro67372 (p : Pattern) (ha : d237827 p = 1) (hb : d267494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237811 q = 1) (hb : d267478 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237811, d267478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237811, d267478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67328 q ha hb
  have h2 (q : Pattern) (ha : d237590 q = 1) (hb : d267314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237590, d267314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67328 q ha hb
    | true =>
      simp only [d237590, d267314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237812 q = 1) (hb : d267479 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237812, d267479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237812, d267479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237591 q = 1) (hb : d267315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237591, d267315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237591, d267315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237813 q = 1) (hb : d267480 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237813, d267480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237813, d267480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237814 q = 1) (hb : d267481 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237814, d267481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237814, d267481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237817 q = 1) (hb : d267484 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237817, d267484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237817, d267484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67329 q ha hb
  have h8 (q : Pattern) (ha : d237599 q = 1) (hb : d267320 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237599, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67329 q ha hb
    | true =>
      simp only [d237599, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237818 q = 1) (hb : d267485 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237818, d267485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237818, d267485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237600 q = 1) (hb : d267321 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237600, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237600, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237819 q = 1) (hb : d267486 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237819, d267486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237819, d267486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d237820 q = 1) (hb : d267487 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237820, d267487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237820, d267487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237821 q = 1) (hb : d267488 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237821, d267488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237821, d267488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237826 q = 1) (hb : d267493 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237826, d267493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237826, d267493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d237827 q = 1) (hb : d267494 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237827, d267494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237827, d267494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro67373 (p : Pattern) (ha : d237841 p = 1) (hb : d267494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237832 q = 1) (hb : d267478 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237832, d267478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237832, d267478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67331 q ha hb
  have h2 (q : Pattern) (ha : d237608 q = 1) (hb : d267314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237608, d267314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67331 q ha hb
    | true =>
      simp only [d237608, d267314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237833 q = 1) (hb : d267479 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237833, d267479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237833, d267479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237609 q = 1) (hb : d267315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237609, d267315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237609, d267315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237834 q = 1) (hb : d267480 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237834, d267480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237834, d267480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237835 q = 1) (hb : d267481 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237835, d267481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237835, d267481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237836 q = 1) (hb : d267484 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237836, d267484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237836, d267484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67332 q ha hb
  have h8 (q : Pattern) (ha : d237613 q = 1) (hb : d267320 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237613, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67332 q ha hb
    | true =>
      simp only [d237613, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237837 q = 1) (hb : d267485 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237837, d267485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237837, d267485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237614 q = 1) (hb : d267321 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237614, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237614, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237838 q = 1) (hb : d267486 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237838, d267486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237838, d267486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d237839 q = 1) (hb : d267487 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237839, d267487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237839, d267487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237840 q = 1) (hb : d267488 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237840, d267488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237840, d267488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237817 q = 1) (hb : d267484 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237817, d267484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237817, d267484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67329 q ha hb
  have h15 (q : Pattern) (ha : d237599 q = 1) (hb : d267320 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237599, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67329 q ha hb
    | true =>
      simp only [d237599, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d237818 q = 1) (hb : d267485 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237818, d267485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d237818, d267485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237600 q = 1) (hb : d267321 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237600, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237600, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d237819 q = 1) (hb : d267486 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237819, d267486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237819, d267486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d237820 q = 1) (hb : d267487 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237820, d267487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d237820, d267487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d237826 q = 1) (hb : d267493 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237826, d267493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d237826, d267493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d237841 q = 1) (hb : d267494 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237841, d267494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237841, d267494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro67374 (p : Pattern) (ha : d237851 p = 1) (hb : d267499 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237836 q = 1) (hb : d267484 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237836, d267484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237836, d267484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67332 q ha hb
  have h2 (q : Pattern) (ha : d237613 q = 1) (hb : d267320 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237613, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67332 q ha hb
    | true =>
      simp only [d237613, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237837 q = 1) (hb : d267485 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237837, d267485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237837, d267485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237614 q = 1) (hb : d267321 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237614, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237614, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237838 q = 1) (hb : d267486 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237838, d267486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237838, d267486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237839 q = 1) (hb : d267487 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237839, d267487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237839, d267487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237845 q = 1) (hb : d267493 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237845, d267493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237845, d267493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d30443 q = 1) (hb : d237846 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30443, d237846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30443, d237846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67334 q ha hb
  have h9 (q : Pattern) (ha : d30135 q = 1) (hb : d237627 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30135, d237627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67334 q ha hb
    | true =>
      simp only [d30135, d237627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30444 q = 1) (hb : d237847 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30444, d237847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30444, d237847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30136 q = 1) (hb : d237628 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30136, d237628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30136, d237628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30445 q = 1) (hb : d237848 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30445, d237848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30445, d237848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30446 q = 1) (hb : d237849 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30446, d237849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30446, d237849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d30447 q = 1) (hb : d237850 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30447, d237850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d30447, d237850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d237851 q = 1) (hb : d267499 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237851, d267499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237851, d267499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro67375 (p : Pattern) (ha : d237857 p = 1) (hb : d267505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237823 q = 1) (hb : d267490 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237823, d267490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67370 q ha hb
    | true =>
      simp only [d237823, d267490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67371 q ha hb
  have h2 (q : Pattern) (ha : d237824 q = 1) (hb : d267491 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237824, d267491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237824, d267491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237825 q = 1) (hb : d267492 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237825, d267492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237825, d267492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237828 q = 1) (hb : d267495 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237828, d267495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67371 q ha hb
    | true =>
      simp only [d237828, d267495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67372 q ha hb
  have h5 (q : Pattern) (ha : d237829 q = 1) (hb : d267496 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237829, d267496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237829, d267496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237830 q = 1) (hb : d267497 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237830, d267497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237830, d267497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237831 q = 1) (hb : d267498 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237831, d267498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237831, d267498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237842 q = 1) (hb : d267495 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237842, d267495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67371 q ha hb
    | true =>
      simp only [d237842, d267495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67373 q ha hb
  have h9 (q : Pattern) (ha : d237843 q = 1) (hb : d267496 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237843, d267496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237843, d267496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237844 q = 1) (hb : d267497 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237844, d267497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237844, d267497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237852 q = 1) (hb : d267500 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237852, d267500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67373 q ha hb
    | true =>
      simp only [d237852, d267500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67374 q ha hb
  have h12 (q : Pattern) (ha : d237853 q = 1) (hb : d267501 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237853, d267501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237853, d267501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237854 q = 1) (hb : d267502 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237854, d267502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237854, d267502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237855 q = 1) (hb : d267503 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237855, d267503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237855, d267503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d237856 q = 1) (hb : d267504 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237856, d267504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237856, d267504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d237857 q = 1) (hb : d267505 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237857, d267505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237857, d267505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro67376 (p : Pattern) (ha : d237862 p = 1) (hb : d267510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237842 q = 1) (hb : d267495 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237842, d267495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67371 q ha hb
    | true =>
      simp only [d237842, d267495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67373 q ha hb
  have h2 (q : Pattern) (ha : d237843 q = 1) (hb : d267496 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237843, d267496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237843, d267496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237844 q = 1) (hb : d267497 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237844, d267497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237844, d267497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237852 q = 1) (hb : d267500 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237852, d267500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67373 q ha hb
    | true =>
      simp only [d237852, d267500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67374 q ha hb
  have h5 (q : Pattern) (ha : d237853 q = 1) (hb : d267501 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237853, d267501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237853, d267501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237854 q = 1) (hb : d267502 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237854, d267502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237854, d267502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237855 q = 1) (hb : d267503 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237855, d267503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237855, d267503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237860 q = 1) (hb : d267508 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237860, d267508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237860, d267508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237861 q = 1) (hb : d267509 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237861, d267509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237861, d267509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237862 q = 1) (hb : d267510 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237862, d267510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237862, d267510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro67377 (p : Pattern) (ha : d237868 p = 1) (hb : d267516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237858 q = 1) (hb : d267506 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237858, d267506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67375 q ha hb
    | true =>
      simp only [d237858, d267506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237859 q = 1) (hb : d267507 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237859, d267507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237859, d267507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237863 q = 1) (hb : d267511 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237863, d267511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67376 q ha hb
    | true =>
      simp only [d237863, d267511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237864 q = 1) (hb : d267512 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237864, d267512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237864, d267512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237865 q = 1) (hb : d267513 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237865, d267513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237865, d267513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237866 q = 1) (hb : d267514 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237866, d267514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237866, d267514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237867 q = 1) (hb : d267515 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237867, d267515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237867, d267515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237868 q = 1) (hb : d267516 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237868, d267516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237868, d267516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro67378 (p : Pattern) (ha : d237870 p = 1) (hb : d267518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237852 q = 1) (hb : d267500 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237852, d267500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67373 q ha hb
    | true =>
      simp only [d237852, d267500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67374 q ha hb
  have h2 (q : Pattern) (ha : d237853 q = 1) (hb : d267501 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237853, d267501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237853, d267501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237854 q = 1) (hb : d267502 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237854, d267502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237854, d267502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237860 q = 1) (hb : d267508 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237860, d267508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237860, d267508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237869 q = 1) (hb : d267517 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237869, d267517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237869, d267517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237870 q = 1) (hb : d267518 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237870, d267518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237870, d267518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67379 (p : Pattern) (ha : d237876 p = 1) (hb : d267524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237863 q = 1) (hb : d267511 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237863, d267511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67376 q ha hb
    | true =>
      simp only [d237863, d267511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237864 q = 1) (hb : d267512 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237864, d267512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237864, d267512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237871 q = 1) (hb : d267519 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237871, d267519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67378 q ha hb
    | true =>
      simp only [d237871, d267519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237872 q = 1) (hb : d267520 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237872, d267520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237872, d267520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237873 q = 1) (hb : d267521 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237873, d267521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237873, d267521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237874 q = 1) (hb : d267522 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237874, d267522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237874, d267522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237875 q = 1) (hb : d267523 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237875, d267523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237875, d267523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237876 q = 1) (hb : d267524 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237876, d267524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237876, d267524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro67380 (p : Pattern) (ha : d237889 p = 1) (hb : d267532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237832 q = 1) (hb : d267478 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237832, d267478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237832, d267478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67331 q ha hb
  have h2 (q : Pattern) (ha : d237608 q = 1) (hb : d267314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237608, d267314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67331 q ha hb
    | true =>
      simp only [d237608, d267314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237833 q = 1) (hb : d267479 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237833, d267479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237833, d267479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237609 q = 1) (hb : d267315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237609, d267315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237609, d267315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237834 q = 1) (hb : d267480 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237834, d267480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237834, d267480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237835 q = 1) (hb : d267481 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237835, d267481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237835, d267481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237836 q = 1) (hb : d267484 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237836, d267484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237836, d267484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67332 q ha hb
  have h8 (q : Pattern) (ha : d237613 q = 1) (hb : d267320 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237613, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67332 q ha hb
    | true =>
      simp only [d237613, d267320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d237837 q = 1) (hb : d267485 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237837, d267485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237837, d267485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237614 q = 1) (hb : d267321 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237614, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237614, d267321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d237838 q = 1) (hb : d267486 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237838, d267486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237838, d267486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d237839 q = 1) (hb : d267487 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237839, d267487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237839, d267487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d237840 q = 1) (hb : d267488 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237840, d267488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237840, d267488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237884 q = 1) (hb : d267527 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237884, d267527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237884, d267527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67352 q ha hb
  have h15 (q : Pattern) (ha : d237721 q = 1) (hb : d267405 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237721, d267405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67352 q ha hb
    | true =>
      simp only [d237721, d267405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d237885 q = 1) (hb : d267528 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237885, d267528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d237885, d267528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237722 q = 1) (hb : d267406 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237722, d267406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237722, d267406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d237886 q = 1) (hb : d267529 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237886, d267529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237886, d267529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d237887 q = 1) (hb : d267530 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237887, d267530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d237887, d267530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d237888 q = 1) (hb : d267531 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237888, d267531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d237888, d267531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d237889 q = 1) (hb : d267532 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237889, d267532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237889, d267532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro67381 (p : Pattern) (ha : d237895 p = 1) (hb : d267533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237890 q = 1) (hb : d267527 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237890, d267527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237890, d267527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67354 q ha hb
  have h2 (q : Pattern) (ha : d237730 q = 1) (hb : d267405 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d237730, d267405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67354 q ha hb
    | true =>
      simp only [d237730, d267405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237891 q = 1) (hb : d267528 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237891, d267528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237891, d267528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237731 q = 1) (hb : d267406 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d237731, d267406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237731, d267406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237892 q = 1) (hb : d267529 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d237892, d267529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237892, d267529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237893 q = 1) (hb : d267530 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d237893, d267530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237893, d267530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d237894 q = 1) (hb : d267531 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d237894, d267531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237894, d267531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d237895 q = 1) (hb : d267533 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d237895, d267533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237895, d267533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro67382 (p : Pattern) (ha : d237901 p = 1) (hb : d267539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237842 q = 1) (hb : d267495 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237842, d267495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67371 q ha hb
    | true =>
      simp only [d237842, d267495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67373 q ha hb
  have h2 (q : Pattern) (ha : d237843 q = 1) (hb : d267496 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237843, d267496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237843, d267496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237844 q = 1) (hb : d267497 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237844, d267497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237844, d267497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237852 q = 1) (hb : d267500 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237852, d267500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67373 q ha hb
    | true =>
      simp only [d237852, d267500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67374 q ha hb
  have h5 (q : Pattern) (ha : d237853 q = 1) (hb : d267501 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237853, d267501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237853, d267501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237854 q = 1) (hb : d267502 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237854, d267502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237854, d267502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237855 q = 1) (hb : d267503 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237855, d267503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237855, d267503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237896 q = 1) (hb : d267534 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d237896, d267534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67380 q ha hb
    | true =>
      simp only [d237896, d267534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67381 q ha hb
  have h9 (q : Pattern) (ha : d237897 q = 1) (hb : d267535 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d237897, d267535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237897, d267535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237898 q = 1) (hb : d267536 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d237898, d267536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237898, d267536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237899 q = 1) (hb : d267537 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d237899, d267537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237899, d267537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d237900 q = 1) (hb : d267538 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d237900, d267538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237900, d267538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237901 q = 1) (hb : d267539 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237901, d267539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237901, d267539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro67383 (p : Pattern) (ha : d237907 p = 1) (hb : d267545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237902 q = 1) (hb : d267540 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237902, d267540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67382 q ha hb
    | true =>
      simp only [d237902, d267540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237903 q = 1) (hb : d267541 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237903, d267541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237903, d267541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237904 q = 1) (hb : d267542 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237904, d267542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237904, d267542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237905 q = 1) (hb : d267543 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237905, d267543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237905, d267543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237906 q = 1) (hb : d267544 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237906, d267544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237906, d267544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237907 q = 1) (hb : d267545 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237907, d267545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237907, d267545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67384 (p : Pattern) (ha : d237913 p = 1) (hb : d267551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237877 q = 1) (hb : d267525 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237877, d267525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67377 q ha hb
    | true =>
      simp only [d237877, d267525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67379 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237882 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d237883 q = 1) (hb : d267526 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237883, d267526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237883, d267526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d237908 q = 1) (hb : d267546 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237908, d267546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67383 q ha hb
    | true =>
      simp only [d237908, d267546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237909 q = 1) (hb : d267547 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237909, d267547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237909, d267547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237910 q = 1) (hb : d267548 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237910, d267548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237910, d267548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237911 q = 1) (hb : d267549 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237911, d267549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237911, d267549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237912 q = 1) (hb : d267550 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237912, d267550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237912, d267550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237913 q = 1) (hb : d267551 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237913, d267551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237913, d267551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro67385 (p : Pattern) (ha : d237881 p = 1) (hb : d267556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237871 q = 1) (hb : d267519 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d237871, d267519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67378 q ha hb
    | true =>
      simp only [d237871, d267519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237872 q = 1) (hb : d267520 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d237872, d267520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237872, d267520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237878 q = 1) (hb : d267553 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d237878, d267553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237878, d267553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237879 q = 1) (hb : d267554 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d237879, d267554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237879, d267554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237880 q = 1) (hb : d267555 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d237880, d267555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237880, d267555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237881 q = 1) (hb : d267556 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d237881, d267556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237881, d267556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67386 (p : Pattern) (ha : d237920 p = 1) (hb : d267562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237915 q = 1) (hb : d267557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237915, d267557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67385 q ha hb
    | true =>
      simp only [d237915, d267557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237916 q = 1) (hb : d267558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237916, d267558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237916, d267558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237917 q = 1) (hb : d267559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237917, d267559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237917, d267559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237918 q = 1) (hb : d267560 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237918, d267560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237918, d267560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237919 q = 1) (hb : d267561 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237919, d267561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237919, d267561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237920 q = 1) (hb : d267562 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237920, d267562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237920, d267562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67387 (p : Pattern) (ha : d237926 p = 1) (hb : d267568 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237660 q = 1) (hb : d267359 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237660, d267359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237660, d267359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67340 q ha hb
  have h2 (q : Pattern) (ha : d237661 q = 1) (hb : d267360 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237661, d267360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237661, d267360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237670 q = 1) (hb : d267369 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237670, d267369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67340 q ha hb
    | true =>
      simp only [d237670, d267369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67343 q ha hb
  have h4 (q : Pattern) (ha : d237671 q = 1) (hb : d267370 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237671, d267370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237671, d267370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237672 q = 1) (hb : d267371 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237672, d267371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237672, d267371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237775 q = 1) (hb : d267451 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237775, d267451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67358 q ha hb
    | true =>
      simp only [d237775, d267451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67365 q ha hb
  have h7 (q : Pattern) (ha : d237788 q = 1) (hb : d267464 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237788, d267464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67366 q ha hb
    | true =>
      simp only [d237788, d267464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67367 q ha hb
  have h8 (q : Pattern) (ha : d237789 q = 1) (hb : d267465 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237789, d267465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237789, d267465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237790 q = 1) (hb : d267466 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237790, d267466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237790, d267466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d237791 q = 1) (hb : d267467 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237791, d267467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237791, d267467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237795 q = 1) (hb : d267471 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237795, d267471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237795, d267471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67368 q ha hb
  have h12 (q : Pattern) (ha : d237797 q = 1) (hb : d267473 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237797, d267473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237797, d267473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67369 q ha hb
  have h13 (q : Pattern) (ha : d237798 q = 1) (hb : d267474 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237798, d267474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d237798, d267474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237799 q = 1) (hb : d267475 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237799, d267475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237799, d267475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d237800 q = 1) (hb : d267476 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237800, d267476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d237800, d267476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d237801 q = 1) (hb : d267477 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237801, d267477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237801, d267477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237914 q = 1) (hb : d267552 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237914, d267552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237914, d267552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67384 q ha hb
  have h18 (q : Pattern) (ha : d237921 q = 1) (hb : d267563 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237921, d267563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237921, d267563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67386 q ha hb
  have h19 (q : Pattern) (ha : d237922 q = 1) (hb : d267564 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237922, d267564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d237922, d267564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d237923 q = 1) (hb : d267565 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237923, d267565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d237923, d267565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d237924 q = 1) (hb : d267566 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237924, d267566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d237924, d267566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d237925 q = 1) (hb : d267567 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237925, d267567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d237925, d267567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d237926 q = 1) (hb : d267568 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d237926, d267568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237926, d267568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro67388 (p : Pattern) (ha : d237932 p = 1) (hb : d267574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237927 q = 1) (hb : d267569 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d237927, d267569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237927, d267569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67387 q ha hb
  have h2 (q : Pattern) (ha : d237928 q = 1) (hb : d267570 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d237928, d267570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237928, d267570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237929 q = 1) (hb : d267571 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d237929, d267571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237929, d267571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237930 q = 1) (hb : d267572 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d237930, d267572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237930, d267572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237931 q = 1) (hb : d267573 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d237931, d267573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237931, d267573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237932 q = 1) (hb : d267574 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d237932, d267574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237932, d267574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67389 (p : Pattern) (ha : d237938 p = 1) (hb : d267580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d236679 q = 1) (hb : d266496 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d236679, d266496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67112 q ha hb
    | true =>
      simp only [d236679, d266496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67155 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d236874 q = 1) (hb : d266732 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d236874, d266732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d236874, d266732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67204 q ha hb
  have h3 (q : Pattern) (ha : d236875 q = 1) (hb : d266733 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d236875, d266733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236875, d266733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237177 q = 1) (hb : d266993 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d237177, d266993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237177, d266993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67261 q ha hb
  have h5 (q : Pattern) (ha : d237178 q = 1) (hb : d266994 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d237178, d266994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237178, d266994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237179 q = 1) (hb : d266995 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d237179, d266995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237179, d266995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237565 q = 1) (hb : d267309 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d237565, d267309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237565, d267309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67326 q ha hb
  have h8 (q : Pattern) (ha : d237566 q = 1) (hb : d267310 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d237566, d267310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237566, d267310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237567 q = 1) (hb : d267311 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d237567, d267311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237567, d267311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237568 q = 1) (hb : d267312 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d237568, d267312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237568, d267312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237933 q = 1) (hb : d267575 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d237933, d267575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237933, d267575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67388 q ha hb
  have h12 (q : Pattern) (ha : d237934 q = 1) (hb : d267576 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d237934, d267576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237934, d267576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237935 q = 1) (hb : d267577 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d237935, d267577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237935, d267577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237936 q = 1) (hb : d267578 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d237936, d267578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237936, d267578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d237937 q = 1) (hb : d267579 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d237937, d267579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237937, d267579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d237938 q = 1) (hb : d267580 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d237938, d267580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237938, d267580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro67390 (p : Pattern) (ha : d237944 p = 1) (hb : d267586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237939 q = 1) (hb : d267581 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d237939, d267581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67389 q ha hb
    | true =>
      simp only [d237939, d267581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237940 q = 1) (hb : d267582 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d237940, d267582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237940, d267582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237941 q = 1) (hb : d267583 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d237941, d267583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237941, d267583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237942 q = 1) (hb : d267584 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d237942, d267584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237942, d267584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237943 q = 1) (hb : d267585 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d237943, d267585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237943, d267585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237944 q = 1) (hb : d267586 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d237944, d267586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237944, d267586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67391 (p : Pattern) (ha : d237950 p = 1) (hb : d267592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237945 q = 1) (hb : d267587 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d237945, d267587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67390 q ha hb
    | true =>
      simp only [d237945, d267587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237946 q = 1) (hb : d267588 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d237946, d267588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237946, d267588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237947 q = 1) (hb : d267589 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d237947, d267589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237947, d267589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237948 q = 1) (hb : d267590 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d237948, d267590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237948, d267590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237949 q = 1) (hb : d267591 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d237949, d267591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237949, d267591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237950 q = 1) (hb : d267592 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d237950, d267592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237950, d267592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67392 (p : Pattern) (ha : d237956 p = 1) (hb : d267598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237951 q = 1) (hb : d267593 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d237951, d267593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67391 q ha hb
    | true =>
      simp only [d237951, d267593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237952 q = 1) (hb : d267594 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d237952, d267594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237952, d267594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237953 q = 1) (hb : d267595 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d237953, d267595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237953, d267595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237954 q = 1) (hb : d267596 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d237954, d267596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237954, d267596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237955 q = 1) (hb : d267597 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d237955, d267597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237955, d267597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237956 q = 1) (hb : d267598 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d237956, d267598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237956, d267598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67393 (p : Pattern) (ha : d237962 p = 1) (hb : d267604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237957 q = 1) (hb : d267599 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d237957, d267599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67392 q ha hb
    | true =>
      simp only [d237957, d267599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237958 q = 1) (hb : d267600 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d237958, d267600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237958, d267600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237959 q = 1) (hb : d267601 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d237959, d267601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237959, d267601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237960 q = 1) (hb : d267602 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d237960, d267602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237960, d267602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237961 q = 1) (hb : d267603 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d237961, d267603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237961, d267603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237962 q = 1) (hb : d267604 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d237962, d267604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237962, d267604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67394 (p : Pattern) (ha : d237968 p = 1) (hb : d267610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237963 q = 1) (hb : d267605 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d237963, d267605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67393 q ha hb
    | true =>
      simp only [d237963, d267605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237964 q = 1) (hb : d267606 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d237964, d267606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237964, d267606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237965 q = 1) (hb : d267607 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d237965, d267607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237965, d267607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237966 q = 1) (hb : d267608 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d237966, d267608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237966, d267608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237967 q = 1) (hb : d267609 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d237967, d267609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237967, d267609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237968 q = 1) (hb : d267610 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d237968, d267610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237968, d267610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67395 (p : Pattern) (ha : d237974 p = 1) (hb : d267616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237969 q = 1) (hb : d267611 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d237969, d267611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67394 q ha hb
    | true =>
      simp only [d237969, d267611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237970 q = 1) (hb : d267612 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d237970, d267612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237970, d267612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237971 q = 1) (hb : d267613 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d237971, d267613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237971, d267613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237972 q = 1) (hb : d267614 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d237972, d267614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237972, d267614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237973 q = 1) (hb : d267615 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d237973, d267615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237973, d267615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237974 q = 1) (hb : d267616 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d237974, d267616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237974, d267616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67396 (p : Pattern) (ha : d237980 p = 1) (hb : d267622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237975 q = 1) (hb : d267617 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d237975, d267617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67395 q ha hb
    | true =>
      simp only [d237975, d267617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237976 q = 1) (hb : d267618 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d237976, d267618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237976, d267618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237977 q = 1) (hb : d267619 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d237977, d267619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237977, d267619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237978 q = 1) (hb : d267620 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d237978, d267620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237978, d267620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237979 q = 1) (hb : d267621 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d237979, d267621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237979, d267621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237980 q = 1) (hb : d267622 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d237980, d267622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237980, d267622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67397 (p : Pattern) (ha : d245707 p = 1) (hb : d266246 p = 1) : d267625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25401 q = 1) (hb : d266246 q = 1) : d25401 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25402 q = 1) (hb : d266246 q = 1) : d266344 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25402, d266344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66811 q ha hb
    | true =>
      simp only [d25402, d266344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25403 q = 1) (hb : d266246 q = 1) : d266345 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25403, d266345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25403, d266345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25404 q = 1) (hb : d266246 q = 1) : d266346 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25404, d266346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25404, d266346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25405 q = 1) (hb : d266246 q = 1) : d266347 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25405, d266347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25405, d266347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25406 q = 1) (hb : d266246 q = 1) : d266348 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25406, d266348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25406, d266348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245707 q = 1) (hb : d266246 q = 1) : d267625 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245707, d267625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245707, d267625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro67398 (p : Pattern) (ha : d245718 p = 1) (hb : d266246 p = 1) : d267636 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25670 q = 1) (hb : d266246 q = 1) : d25670 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d245713 q = 1) (hb : d266246 q = 1) : d267631 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245713, d267631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66833 q ha hb
    | true =>
      simp only [d245713, d267631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245714 q = 1) (hb : d266246 q = 1) : d267632 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245714, d267632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245714, d267632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245715 q = 1) (hb : d266246 q = 1) : d267633 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245715, d267633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245715, d267633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245716 q = 1) (hb : d266246 q = 1) : d267634 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245716, d267634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245716, d267634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245717 q = 1) (hb : d266246 q = 1) : d267635 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245717, d267635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245717, d267635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245718 q = 1) (hb : d266246 q = 1) : d267636 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245718, d267636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245718, d267636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro67399 (p : Pattern) (ha : d245724 p = 1) (hb : d266246 p = 1) : d267642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25408 q = 1) (hb : d266246 q = 1) : d266350 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25408, d266350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66810 q ha hb
    | true =>
      simp only [d25408, d266350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66812 q ha hb
  have h2 (q : Pattern) (ha : d25409 q = 1) (hb : d266246 q = 1) : d266351 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25409, d266351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25409, d266351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245705 q = 1) (hb : d266246 q = 1) : d267623 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245705, d267623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245705, d267623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245706 q = 1) (hb : d266246 q = 1) : d267624 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245706, d267624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245706, d267624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245708 q = 1) (hb : d266246 q = 1) : d267626 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245708, d267626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245708, d267626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67397 q ha hb
  have h6 (q : Pattern) (ha : d245709 q = 1) (hb : d266246 q = 1) : d267627 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245709, d267627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245709, d267627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d245710 q = 1) (hb : d266246 q = 1) : d267628 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245710, d267628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245710, d267628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d245711 q = 1) (hb : d266246 q = 1) : d267629 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245711, d267629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245711, d267629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d245712 q = 1) (hb : d266246 q = 1) : d267630 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245712, d267630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245712, d267630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245719 q = 1) (hb : d266246 q = 1) : d267637 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245719, d267637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245719, d267637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67398 q ha hb
  have h11 (q : Pattern) (ha : d245720 q = 1) (hb : d266246 q = 1) : d267638 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245720, d267638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245720, d267638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245721 q = 1) (hb : d266246 q = 1) : d267639 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245721, d267639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245721, d267639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d245722 q = 1) (hb : d266246 q = 1) : d267640 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245722, d267640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245722, d267640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d245723 q = 1) (hb : d266246 q = 1) : d267641 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245723, d267641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245723, d267641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245724 q = 1) (hb : d266246 q = 1) : d267642 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245724, d267642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245724, d267642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro67400 (p : Pattern) (ha : d245730 p = 1) (hb : d266246 p = 1) : d267648 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245725 q = 1) (hb : d266246 q = 1) : d267643 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245725, d267643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245725, d267643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67399 q ha hb
  have h2 (q : Pattern) (ha : d245726 q = 1) (hb : d266246 q = 1) : d267644 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245726, d267644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245726, d267644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245727 q = 1) (hb : d266246 q = 1) : d267645 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245727, d267645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245727, d267645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245728 q = 1) (hb : d266246 q = 1) : d267646 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245728, d267646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245728, d267646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245729 q = 1) (hb : d266246 q = 1) : d267647 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245729, d267647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245729, d267647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245730 q = 1) (hb : d266246 q = 1) : d267648 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245730, d267648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245730, d267648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67401 (p : Pattern) (ha : d245734 p = 1) (hb : d266246 p = 1) : d267652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25735 q = 1) (hb : d266246 q = 1) : d266534 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25735, d266534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66845 q ha hb
    | true =>
      simp only [d25735, d266534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66846 q ha hb
  have h2 (q : Pattern) (ha : d25736 q = 1) (hb : d266246 q = 1) : d266535 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25736, d266535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25736, d266535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25737 q = 1) (hb : d266246 q = 1) : d266536 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25737, d266536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25737, d266536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25738 q = 1) (hb : d266246 q = 1) : d266537 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25738, d266537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25738, d266537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25739 q = 1) (hb : d266246 q = 1) : d266538 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25739, d266538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25739, d266538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245734 q = 1) (hb : d266246 q = 1) : d267652 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245734, d267652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245734, d267652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67402 (p : Pattern) (ha : d245745 p = 1) (hb : d266246 p = 1) : d267663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245740 q = 1) (hb : d266246 q = 1) : d267658 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245740, d267658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66879 q ha hb
    | true =>
      simp only [d245740, d267658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66853 q ha hb
  have h2 (q : Pattern) (ha : d245741 q = 1) (hb : d266246 q = 1) : d267659 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245741, d267659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245741, d267659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245742 q = 1) (hb : d266246 q = 1) : d267660 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245742, d267660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245742, d267660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245743 q = 1) (hb : d266246 q = 1) : d267661 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245743, d267661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245743, d267661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245744 q = 1) (hb : d266246 q = 1) : d267662 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245744, d267662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245744, d267662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245745 q = 1) (hb : d266246 q = 1) : d267663 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245745, d267663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245745, d267663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67403 (p : Pattern) (ha : d245751 p = 1) (hb : d266246 p = 1) : d267669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25741 q = 1) (hb : d266246 q = 1) : d266540 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25741, d266540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66844 q ha hb
    | true =>
      simp only [d25741, d266540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66847 q ha hb
  have h2 (q : Pattern) (ha : d25742 q = 1) (hb : d266246 q = 1) : d266541 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25742, d266541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25742, d266541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245732 q = 1) (hb : d266246 q = 1) : d267650 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245732, d267650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245732, d267650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245733 q = 1) (hb : d266246 q = 1) : d267651 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245733, d267651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245733, d267651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245735 q = 1) (hb : d266246 q = 1) : d267653 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245735, d267653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245735, d267653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67401 q ha hb
  have h6 (q : Pattern) (ha : d245736 q = 1) (hb : d266246 q = 1) : d267654 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245736, d267654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245736, d267654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d245737 q = 1) (hb : d266246 q = 1) : d267655 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245737, d267655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245737, d267655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d245738 q = 1) (hb : d266246 q = 1) : d267656 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245738, d267656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245738, d267656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d245739 q = 1) (hb : d266246 q = 1) : d267657 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245739, d267657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245739, d267657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245746 q = 1) (hb : d266246 q = 1) : d267664 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245746, d267664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245746, d267664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67402 q ha hb
  have h11 (q : Pattern) (ha : d245747 q = 1) (hb : d266246 q = 1) : d267665 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245747, d267665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245747, d267665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245748 q = 1) (hb : d266246 q = 1) : d267666 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245748, d267666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245748, d267666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d245749 q = 1) (hb : d266246 q = 1) : d267667 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245749, d267667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245749, d267667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d245750 q = 1) (hb : d266246 q = 1) : d267668 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245750, d267668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245750, d267668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245751 q = 1) (hb : d266246 q = 1) : d267669 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245751, d267669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245751, d267669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro67404 (p : Pattern) (ha : d245757 p = 1) (hb : d266246 p = 1) : d267675 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245752 q = 1) (hb : d266246 q = 1) : d267670 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245752, d267670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245752, d267670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67403 q ha hb
  have h2 (q : Pattern) (ha : d245753 q = 1) (hb : d266246 q = 1) : d267671 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245753, d267671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245753, d267671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245754 q = 1) (hb : d266246 q = 1) : d267672 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245754, d267672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245754, d267672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245755 q = 1) (hb : d266246 q = 1) : d267673 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245755, d267673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245755, d267673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245756 q = 1) (hb : d266246 q = 1) : d267674 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245756, d267674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245756, d267674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245757 q = 1) (hb : d266246 q = 1) : d267675 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245757, d267675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245757, d267675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67405 (p : Pattern) (ha : d245762 p = 1) (hb : d266246 p = 1) : d267680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26159 q = 1) (hb : d266246 q = 1) : d266779 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26159, d266779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66898 q ha hb
    | true =>
      simp only [d26159, d266779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66899 q ha hb
  have h2 (q : Pattern) (ha : d26160 q = 1) (hb : d266246 q = 1) : d266780 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26160, d266780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26160, d266780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26161 q = 1) (hb : d266246 q = 1) : d266781 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26161, d266781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26161, d266781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26162 q = 1) (hb : d266246 q = 1) : d266782 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26162, d266782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26162, d266782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26163 q = 1) (hb : d266246 q = 1) : d266783 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26163, d266783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26163, d266783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245762 q = 1) (hb : d266246 q = 1) : d267680 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245762, d267680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245762, d267680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67406 (p : Pattern) (ha : d245773 p = 1) (hb : d266246 p = 1) : d267691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245768 q = 1) (hb : d266246 q = 1) : d267686 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245768, d267686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66938 q ha hb
    | true =>
      simp only [d245768, d267686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66907 q ha hb
  have h2 (q : Pattern) (ha : d245769 q = 1) (hb : d266246 q = 1) : d267687 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245769, d267687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245769, d267687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245770 q = 1) (hb : d266246 q = 1) : d267688 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245770, d267688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245770, d267688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245771 q = 1) (hb : d266246 q = 1) : d267689 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245771, d267689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245771, d267689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245772 q = 1) (hb : d266246 q = 1) : d267690 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245772, d267690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245772, d267690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245773 q = 1) (hb : d266246 q = 1) : d267691 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245773, d267691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245773, d267691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67407 (p : Pattern) (ha : d245779 p = 1) (hb : d266246 p = 1) : d267697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26165 q = 1) (hb : d266246 q = 1) : d266785 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26165, d266785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66897 q ha hb
    | true =>
      simp only [d26165, d266785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66900 q ha hb
  have h2 (q : Pattern) (ha : d26166 q = 1) (hb : d266246 q = 1) : d266786 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d26166, d266786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26166, d266786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245760 q = 1) (hb : d266246 q = 1) : d267678 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245760, d267678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245760, d267678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245761 q = 1) (hb : d266246 q = 1) : d267679 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245761, d267679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245761, d267679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245763 q = 1) (hb : d266246 q = 1) : d267681 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245763, d267681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245763, d267681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67405 q ha hb
  have h6 (q : Pattern) (ha : d245764 q = 1) (hb : d266246 q = 1) : d267682 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245764, d267682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245764, d267682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d245765 q = 1) (hb : d266246 q = 1) : d267683 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245765, d267683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245765, d267683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d245766 q = 1) (hb : d266246 q = 1) : d267684 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245766, d267684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245766, d267684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d245767 q = 1) (hb : d266246 q = 1) : d267685 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245767, d267685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245767, d267685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245774 q = 1) (hb : d266246 q = 1) : d267692 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245774, d267692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245774, d267692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67406 q ha hb
  have h11 (q : Pattern) (ha : d245775 q = 1) (hb : d266246 q = 1) : d267693 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245775, d267693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245775, d267693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245776 q = 1) (hb : d266246 q = 1) : d267694 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245776, d267694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245776, d267694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d245777 q = 1) (hb : d266246 q = 1) : d267695 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245777, d267695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245777, d267695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d245778 q = 1) (hb : d266246 q = 1) : d267696 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245778, d267696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245778, d267696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245779 q = 1) (hb : d266246 q = 1) : d267697 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245779, d267697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245779, d267697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro67408 (p : Pattern) (ha : d245785 p = 1) (hb : d266246 p = 1) : d267703 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245780 q = 1) (hb : d266246 q = 1) : d267698 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245780, d267698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245780, d267698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67407 q ha hb
  have h2 (q : Pattern) (ha : d245781 q = 1) (hb : d266246 q = 1) : d267699 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245781, d267699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245781, d267699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245782 q = 1) (hb : d266246 q = 1) : d267700 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245782, d267700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245782, d267700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245783 q = 1) (hb : d266246 q = 1) : d267701 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245783, d267701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245783, d267701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245784 q = 1) (hb : d266246 q = 1) : d267702 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245784, d267702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245784, d267702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245785 q = 1) (hb : d266246 q = 1) : d267703 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245785, d267703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245785, d267703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67409 (p : Pattern) (ha : d245791 p = 1) (hb : d266246 p = 1) : d267709 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26626 q = 1) (hb : d266246 q = 1) : d267072 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26626, d267072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66959 q ha hb
    | true =>
      simp only [d26626, d267072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66960 q ha hb
  have h2 (q : Pattern) (ha : d26627 q = 1) (hb : d266246 q = 1) : d267073 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26627, d267073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26627, d267073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26628 q = 1) (hb : d266246 q = 1) : d267074 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26628, d267074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26628, d267074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26629 q = 1) (hb : d266246 q = 1) : d267075 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26629, d267075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26629, d267075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26630 q = 1) (hb : d266246 q = 1) : d267076 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26630, d267076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26630, d267076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245791 q = 1) (hb : d266246 q = 1) : d267709 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245791, d267709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245791, d267709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67410 (p : Pattern) (ha : d245802 p = 1) (hb : d266246 p = 1) : d267720 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245797 q = 1) (hb : d266246 q = 1) : d267715 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245797, d267715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66999 q ha hb
    | true =>
      simp only [d245797, d267715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66968 q ha hb
  have h2 (q : Pattern) (ha : d245798 q = 1) (hb : d266246 q = 1) : d267716 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245798, d267716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245798, d267716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245799 q = 1) (hb : d266246 q = 1) : d267717 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245799, d267717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245799, d267717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245800 q = 1) (hb : d266246 q = 1) : d267718 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245800, d267718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245800, d267718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245801 q = 1) (hb : d266246 q = 1) : d267719 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245801, d267719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245801, d267719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245802 q = 1) (hb : d266246 q = 1) : d267720 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245802, d267720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245802, d267720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67411 (p : Pattern) (ha : d245808 p = 1) (hb : d266246 p = 1) : d267726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26632 q = 1) (hb : d266246 q = 1) : d267078 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26632, d267078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66958 q ha hb
    | true =>
      simp only [d26632, d267078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66961 q ha hb
  have h2 (q : Pattern) (ha : d26633 q = 1) (hb : d266246 q = 1) : d267079 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d26633, d267079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26633, d267079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245789 q = 1) (hb : d266246 q = 1) : d267707 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245789, d267707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245789, d267707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245790 q = 1) (hb : d266246 q = 1) : d267708 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245790, d267708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245790, d267708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245792 q = 1) (hb : d266246 q = 1) : d267710 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245792, d267710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245792, d267710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67409 q ha hb
  have h6 (q : Pattern) (ha : d245793 q = 1) (hb : d266246 q = 1) : d267711 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245793, d267711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245793, d267711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d245794 q = 1) (hb : d266246 q = 1) : d267712 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245794, d267712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245794, d267712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d245795 q = 1) (hb : d266246 q = 1) : d267713 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245795, d267713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245795, d267713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d245796 q = 1) (hb : d266246 q = 1) : d267714 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245796, d267714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245796, d267714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245803 q = 1) (hb : d266246 q = 1) : d267721 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245803, d267721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245803, d267721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67410 q ha hb
  have h11 (q : Pattern) (ha : d245804 q = 1) (hb : d266246 q = 1) : d267722 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245804, d267722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245804, d267722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245805 q = 1) (hb : d266246 q = 1) : d267723 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245805, d267723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245805, d267723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d245806 q = 1) (hb : d266246 q = 1) : d267724 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245806, d267724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245806, d267724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d245807 q = 1) (hb : d266246 q = 1) : d267725 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245807, d267725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245807, d267725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245808 q = 1) (hb : d266246 q = 1) : d267726 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245808, d267726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245808, d267726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro67412 (p : Pattern) (ha : d245814 p = 1) (hb : d266246 p = 1) : d267732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245809 q = 1) (hb : d266246 q = 1) : d267727 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245809, d267727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245809, d267727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67411 q ha hb
  have h2 (q : Pattern) (ha : d245810 q = 1) (hb : d266246 q = 1) : d267728 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245810, d267728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245810, d267728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245811 q = 1) (hb : d266246 q = 1) : d267729 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245811, d267729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245811, d267729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245812 q = 1) (hb : d266246 q = 1) : d267730 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245812, d267730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245812, d267730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245813 q = 1) (hb : d266246 q = 1) : d267731 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245813, d267731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245813, d267731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245814 q = 1) (hb : d266246 q = 1) : d267732 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245814, d267732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245814, d267732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67413 (p : Pattern) (ha : d245821 p = 1) (hb : d266246 p = 1) : d267739 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27079 q = 1) (hb : d266246 q = 1) : d267363 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27079, d267363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67020 q ha hb
    | true =>
      simp only [d27079, d267363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67021 q ha hb
  have h2 (q : Pattern) (ha : d27080 q = 1) (hb : d266246 q = 1) : d267364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27080, d267364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27080, d267364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27081 q = 1) (hb : d266246 q = 1) : d267365 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27081, d267365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27081, d267365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27082 q = 1) (hb : d266246 q = 1) : d267366 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27082, d267366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27082, d267366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27083 q = 1) (hb : d266246 q = 1) : d267367 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27083, d267367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27083, d267367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245821 q = 1) (hb : d266246 q = 1) : d267739 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245821, d267739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245821, d267739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67414 (p : Pattern) (ha : d245832 p = 1) (hb : d266246 p = 1) : d267750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245827 q = 1) (hb : d266246 q = 1) : d267745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245827, d267745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67060 q ha hb
    | true =>
      simp only [d245827, d267745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67029 q ha hb
  have h2 (q : Pattern) (ha : d245828 q = 1) (hb : d266246 q = 1) : d267746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245828, d267746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245828, d267746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245829 q = 1) (hb : d266246 q = 1) : d267747 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245829, d267747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245829, d267747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245830 q = 1) (hb : d266246 q = 1) : d267748 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245830, d267748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245830, d267748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245831 q = 1) (hb : d266246 q = 1) : d267749 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245831, d267749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245831, d267749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245832 q = 1) (hb : d266246 q = 1) : d267750 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245832, d267750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245832, d267750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67415 (p : Pattern) (ha : d245838 p = 1) (hb : d266246 p = 1) : d267756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27085 q = 1) (hb : d266246 q = 1) : d267369 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27085, d267369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67019 q ha hb
    | true =>
      simp only [d27085, d267369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67022 q ha hb
  have h2 (q : Pattern) (ha : d27086 q = 1) (hb : d266246 q = 1) : d267370 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d27086, d267370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27086, d267370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245819 q = 1) (hb : d266246 q = 1) : d267737 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245819, d267737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245819, d267737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245820 q = 1) (hb : d266246 q = 1) : d267738 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245820, d267738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245820, d267738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245822 q = 1) (hb : d266246 q = 1) : d267740 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245822, d267740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245822, d267740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67413 q ha hb
  have h6 (q : Pattern) (ha : d245823 q = 1) (hb : d266246 q = 1) : d267741 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245823, d267741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245823, d267741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d245824 q = 1) (hb : d266246 q = 1) : d267742 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245824, d267742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245824, d267742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d245825 q = 1) (hb : d266246 q = 1) : d267743 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245825, d267743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245825, d267743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d245826 q = 1) (hb : d266246 q = 1) : d267744 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245826, d267744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245826, d267744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245833 q = 1) (hb : d266246 q = 1) : d267751 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245833, d267751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245833, d267751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67414 q ha hb
  have h11 (q : Pattern) (ha : d245834 q = 1) (hb : d266246 q = 1) : d267752 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245834, d267752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245834, d267752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245835 q = 1) (hb : d266246 q = 1) : d267753 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245835, d267753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245835, d267753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d245836 q = 1) (hb : d266246 q = 1) : d267754 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245836, d267754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245836, d267754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d245837 q = 1) (hb : d266246 q = 1) : d267755 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245837, d267755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245837, d267755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245838 q = 1) (hb : d266246 q = 1) : d267756 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245838, d267756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245838, d267756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro67416 (p : Pattern) (ha : d245844 p = 1) (hb : d266246 p = 1) : d267762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245839 q = 1) (hb : d266246 q = 1) : d267757 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245839, d267757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245839, d267757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67415 q ha hb
  have h2 (q : Pattern) (ha : d245840 q = 1) (hb : d266246 q = 1) : d267758 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245840, d267758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245840, d267758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245841 q = 1) (hb : d266246 q = 1) : d267759 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245841, d267759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245841, d267759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245842 q = 1) (hb : d266246 q = 1) : d267760 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245842, d267760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245842, d267760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245843 q = 1) (hb : d266246 q = 1) : d267761 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245843, d267761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245843, d267761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245844 q = 1) (hb : d266246 q = 1) : d267762 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245844, d267762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245844, d267762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67417 (p : Pattern) (ha : d245850 p = 1) (hb : d266246 p = 1) : d267768 p = 1 := by
  have h0 (q : Pattern) (ha : d245704 q = 1) (hb : d266246 q = 1) : d245704 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245731 q = 1) (hb : d266246 q = 1) : d267649 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245731, d267649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245731, d267649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67400 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d245758 q = 1) (hb : d266246 q = 1) : d267676 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245758, d267676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245758, d267676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67404 q ha hb
  have h4 (q : Pattern) (ha : d245759 q = 1) (hb : d266246 q = 1) : d267677 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245759, d267677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245759, d267677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245786 q = 1) (hb : d266246 q = 1) : d267704 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245786, d267704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245786, d267704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67408 q ha hb
  have h6 (q : Pattern) (ha : d245787 q = 1) (hb : d266246 q = 1) : d267705 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245787, d267705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245787, d267705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245788 q = 1) (hb : d266246 q = 1) : d267706 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245788, d267706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245788, d267706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245815 q = 1) (hb : d266246 q = 1) : d267733 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245815, d267733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245815, d267733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67412 q ha hb
  have h9 (q : Pattern) (ha : d245816 q = 1) (hb : d266246 q = 1) : d267734 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245816, d267734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245816, d267734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245817 q = 1) (hb : d266246 q = 1) : d267735 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245817, d267735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245817, d267735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245818 q = 1) (hb : d266246 q = 1) : d267736 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245818, d267736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245818, d267736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d245845 q = 1) (hb : d266246 q = 1) : d267763 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245845, d267763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245845, d267763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67416 q ha hb
  have h13 (q : Pattern) (ha : d245846 q = 1) (hb : d266246 q = 1) : d267764 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245846, d267764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245846, d267764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245847 q = 1) (hb : d266246 q = 1) : d267765 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245847, d267765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245847, d267765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d245848 q = 1) (hb : d266246 q = 1) : d267766 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245848, d267766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245848, d267766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d245849 q = 1) (hb : d266246 q = 1) : d267767 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d245849, d267767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245849, d267767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245850 q = 1) (hb : d266246 q = 1) : d267768 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d245850, d267768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245850, d267768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h17 p ha hb
theorem andIntro67418 (p : Pattern) (ha : d245856 p = 1) (hb : d266246 p = 1) : d267774 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245851 q = 1) (hb : d266246 q = 1) : d267769 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d245851, d267769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67417 q ha hb
    | true =>
      simp only [d245851, d267769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245852 q = 1) (hb : d266246 q = 1) : d267770 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d245852, d267770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245852, d267770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245853 q = 1) (hb : d266246 q = 1) : d267771 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d245853, d267771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245853, d267771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245854 q = 1) (hb : d266246 q = 1) : d267772 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d245854, d267772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245854, d267772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245855 q = 1) (hb : d266246 q = 1) : d267773 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d245855, d267773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245855, d267773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245856 q = 1) (hb : d266246 q = 1) : d267774 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d245856, d267774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245856, d267774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67419 (p : Pattern) (ha : d245862 p = 1) (hb : d266246 p = 1) : d267780 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245857 q = 1) (hb : d266246 q = 1) : d267775 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d245857, d267775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67418 q ha hb
    | true =>
      simp only [d245857, d267775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245858 q = 1) (hb : d266246 q = 1) : d267776 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d245858, d267776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245858, d267776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245859 q = 1) (hb : d266246 q = 1) : d267777 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d245859, d267777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245859, d267777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245860 q = 1) (hb : d266246 q = 1) : d267778 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d245860, d267778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245860, d267778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245861 q = 1) (hb : d266246 q = 1) : d267779 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d245861, d267779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245861, d267779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245862 q = 1) (hb : d266246 q = 1) : d267780 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d245862, d267780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245862, d267780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67420 (p : Pattern) (ha : d245868 p = 1) (hb : d266246 p = 1) : d267786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245863 q = 1) (hb : d266246 q = 1) : d267781 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d245863, d267781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67419 q ha hb
    | true =>
      simp only [d245863, d267781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245864 q = 1) (hb : d266246 q = 1) : d267782 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d245864, d267782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245864, d267782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245865 q = 1) (hb : d266246 q = 1) : d267783 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d245865, d267783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245865, d267783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245866 q = 1) (hb : d266246 q = 1) : d267784 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d245866, d267784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245866, d267784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245867 q = 1) (hb : d266246 q = 1) : d267785 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d245867, d267785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245867, d267785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245868 q = 1) (hb : d266246 q = 1) : d267786 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d245868, d267786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245868, d267786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67421 (p : Pattern) (ha : d245874 p = 1) (hb : d266246 p = 1) : d267792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245869 q = 1) (hb : d266246 q = 1) : d267787 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d245869, d267787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67420 q ha hb
    | true =>
      simp only [d245869, d267787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245870 q = 1) (hb : d266246 q = 1) : d267788 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d245870, d267788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245870, d267788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245871 q = 1) (hb : d266246 q = 1) : d267789 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d245871, d267789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245871, d267789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245872 q = 1) (hb : d266246 q = 1) : d267790 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d245872, d267790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245872, d267790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245873 q = 1) (hb : d266246 q = 1) : d267791 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d245873, d267791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245873, d267791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245874 q = 1) (hb : d266246 q = 1) : d267792 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d245874, d267792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245874, d267792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67422 (p : Pattern) (ha : d245880 p = 1) (hb : d266246 p = 1) : d267798 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245875 q = 1) (hb : d266246 q = 1) : d267793 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d245875, d267793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67421 q ha hb
    | true =>
      simp only [d245875, d267793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245876 q = 1) (hb : d266246 q = 1) : d267794 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d245876, d267794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245876, d267794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245877 q = 1) (hb : d266246 q = 1) : d267795 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d245877, d267795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245877, d267795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245878 q = 1) (hb : d266246 q = 1) : d267796 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d245878, d267796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245878, d267796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245879 q = 1) (hb : d266246 q = 1) : d267797 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d245879, d267797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245879, d267797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245880 q = 1) (hb : d266246 q = 1) : d267798 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d245880, d267798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245880, d267798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67423 (p : Pattern) (ha : d245886 p = 1) (hb : d266246 p = 1) : d267804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245881 q = 1) (hb : d266246 q = 1) : d267799 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d245881, d267799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67422 q ha hb
    | true =>
      simp only [d245881, d267799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245882 q = 1) (hb : d266246 q = 1) : d267800 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d245882, d267800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245882, d267800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245883 q = 1) (hb : d266246 q = 1) : d267801 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d245883, d267801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245883, d267801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245884 q = 1) (hb : d266246 q = 1) : d267802 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d245884, d267802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245884, d267802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245885 q = 1) (hb : d266246 q = 1) : d267803 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d245885, d267803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245885, d267803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245886 q = 1) (hb : d266246 q = 1) : d267804 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d245886, d267804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245886, d267804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67424 (p : Pattern) (ha : d245892 p = 1) (hb : d266246 p = 1) : d267810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d266246 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245887 q = 1) (hb : d266246 q = 1) : d267805 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d245887, d267805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67423 q ha hb
    | true =>
      simp only [d245887, d267805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d245888 q = 1) (hb : d266246 q = 1) : d267806 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d245888, d267806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245888, d267806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d245889 q = 1) (hb : d266246 q = 1) : d267807 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d245889, d267807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245889, d267807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d245890 q = 1) (hb : d266246 q = 1) : d267808 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d245890, d267808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245890, d267808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245891 q = 1) (hb : d266246 q = 1) : d267809 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d245891, d267809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245891, d267809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d245892 q = 1) (hb : d266246 q = 1) : d267810 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d245892, d267810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245892, d267810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro67425 (p : Pattern) (ha : d25187 p = 1) (hb : d126892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d126887 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25123 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67079 q ha hb
    | true =>
      simp only [d25123, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h5 (q : Pattern) (ha : d25183 q = 1) (hb : d126888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25183, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25184 q = 1) (hb : d126889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25184, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25185 q = 1) (hb : d126890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25185, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25186 q = 1) (hb : d126891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25186, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25187 q = 1) (hb : d126892 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25187, d126892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25187, d126892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro67426 (p : Pattern) (ha : d25194 p = 1) (hb : d126899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126887 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d25123 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67079 q ha hb
    | true =>
      simp only [d25123, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d25183 q = 1) (hb : d126888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25183, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25184 q = 1) (hb : d126889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25184, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25185 q = 1) (hb : d126890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25185, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25186 q = 1) (hb : d126891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25186, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d126894 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d25130 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67081 q ha hb
    | true =>
      simp only [d25130, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h13 (q : Pattern) (ha : d25190 q = 1) (hb : d126895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25190, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25190, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d25191 q = 1) (hb : d126896 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25191, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25191, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25192 q = 1) (hb : d126897 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25192, d126897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25192, d126897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25193 q = 1) (hb : d126898 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25193, d126898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25193, d126898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d25194 q = 1) (hb : d126899 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25194, d126899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25194, d126899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro67427 (p : Pattern) (ha : d126906 p = 1) (hb : d245682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126894 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25130 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67081 q ha hb
    | true =>
      simp only [d25130, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h3 (q : Pattern) (ha : d25190 q = 1) (hb : d126895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25190, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25190, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25191 q = 1) (hb : d126896 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25191, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25191, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25192 q = 1) (hb : d126904 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25192, d126904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25192, d126904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25193 q = 1) (hb : d126905 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25193, d126905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25193, d126905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d126906 q = 1) (hb : d245682 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d126906, d245682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126906, d245682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro67428 (p : Pattern) (ha : d126930 p = 1) (hb : d245692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126925 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25166 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25166, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67086 q ha hb
    | true =>
      simp only [d25166, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h3 (q : Pattern) (ha : d126926 q = 1) (hb : d245688 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d126926, d245688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126926, d245688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74105 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d126927 q = 1) (hb : d245689 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126927, d245689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d126927, d245689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d126928 q = 1) (hb : d245690 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d126928, d245690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126928, d245690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126929 q = 1) (hb : d245691 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d126929, d245691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126929, d245691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d126930 q = 1) (hb : d245692 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d126930, d245692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126930, d245692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67429 (p : Pattern) (ha : d126936 p = 1) (hb : d245698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25195 q = 1) (hb : d126900 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25195, d126900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67425 q ha hb
    | true =>
      simp only [d25195, d126900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67426 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d25196 q = 1) (hb : d126901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25196, d126901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25196, d126901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d126902 q = 1) (hb : d245680 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d126902, d245680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d126902, d245680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d126903 q = 1) (hb : d245681 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d126903, d245681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126903, d245681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126907 q = 1) (hb : d245683 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d126907, d245683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d126907, d245683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67427 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d126908 q = 1) (hb : d245684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d126908, d245684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d126908, d245684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d126909 q = 1) (hb : d245685 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d126909, d245685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d126909, d245685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d126910 q = 1) (hb : d245686 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d126910, d245686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d126910, d245686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d126911 q = 1) (hb : d245687 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d126911, d245687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126911, d245687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d126931 q = 1) (hb : d245693 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d126931, d245693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d126931, d245693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67428 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d126932 q = 1) (hb : d245694 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d126932, d245694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d126932, d245694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d126933 q = 1) (hb : d245695 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d126933, d245695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d126933, d245695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d126934 q = 1) (hb : d245696 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d126934, d245696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d126934, d245696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d126935 q = 1) (hb : d245697 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d126935, d245697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d126935, d245697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d126936 q = 1) (hb : d245698 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d126936, d245698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d126936, d245698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro67430 (p : Pattern) (ha : d126942 p = 1) (hb : d245704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52074 q = 1) (hb : d53648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52074, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52074, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro327 q ha hb
  have h3 (q : Pattern) (ha : d52075 q = 1) (hb : d53649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52075, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52075, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52076 q = 1) (hb : d53650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52076, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52076, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52077 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52077, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52077, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52078 q = 1) (hb : d53652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52078, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52078, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126937 q = 1) (hb : d245699 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d126937, d245699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126937, d245699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67429 q ha hb
  have h8 (q : Pattern) (ha : d126938 q = 1) (hb : d245700 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d126938, d245700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126938, d245700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d126939 q = 1) (hb : d245701 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d126939, d245701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126939, d245701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d126940 q = 1) (hb : d245702 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d126940, d245702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126940, d245702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d126941 q = 1) (hb : d245703 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d126941, d245703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126941, d245703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d126942 q = 1) (hb : d245704 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d126942, d245704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126942, d245704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro67431 (p : Pattern) (ha : d236619 p = 1) (hb : d266340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126980 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d236614 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d126951 q = 1) (hb : d266335 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d126951, d266335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67122 q ha hb
    | true =>
      simp only [d126951, d266335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67114 q hb ha
  have h5 (q : Pattern) (ha : d236615 q = 1) (hb : d266336 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d236615, d266336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d236615, d266336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d127009 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d236616 q = 1) (hb : d266337 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d236616, d266337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d236616, d266337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d236617 q = 1) (hb : d266338 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d236617, d266338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d236617, d266338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d236618 q = 1) (hb : d266339 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d236618, d266339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d236618, d266339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d236619 q = 1) (hb : d266340 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d236619, d266340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236619, d266340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro67432 (p : Pattern) (ha : d236626 p = 1) (hb : d266349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d126974 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d236614 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d126951 q = 1) (hb : d266335 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d126951, d266335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67122 q ha hb
    | true =>
      simp only [d126951, d266335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67114 q hb ha
  have h4 (q : Pattern) (ha : d236615 q = 1) (hb : d266336 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d236615, d266336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d236615, d266336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d127009 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d236616 q = 1) (hb : d266337 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d236616, d266337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d236616, d266337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d236617 q = 1) (hb : d266338 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d236617, d266338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d236617, d266338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d236618 q = 1) (hb : d266339 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d236618, d266339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236618, d266339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127018 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127022 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d236621 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d126960 q = 1) (hb : d266344 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d126960, d266344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67124 q ha hb
    | true =>
      simp only [d126960, d266344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67115 q hb ha
  have h13 (q : Pattern) (ha : d236622 q = 1) (hb : d266345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d236622, d266345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d236622, d266345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127028 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d236623 q = 1) (hb : d266346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d236623, d266346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d236623, d266346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d236624 q = 1) (hb : d266347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d236624, d266347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d236624, d266347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d236625 q = 1) (hb : d266348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d236625, d266348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d236625, d266348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d236626 q = 1) (hb : d266349 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d236626, d266349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d236626, d266349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro67433 (p : Pattern) (ha : d236633 p = 1) (hb : d267625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236621 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126960 q = 1) (hb : d266344 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d126960, d266344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67124 q ha hb
    | true =>
      simp only [d126960, d266344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67115 q hb ha
  have h3 (q : Pattern) (ha : d236622 q = 1) (hb : d266345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d236622, d266345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d236622, d266345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127028 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d236623 q = 1) (hb : d266346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d236623, d266346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236623, d266346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d236631 q = 1) (hb : d266347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d236631, d266347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236631, d266347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d236632 q = 1) (hb : d266348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d236632, d266348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236632, d266348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d236633 q = 1) (hb : d267625 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d236633, d267625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236633, d267625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67434 (p : Pattern) (ha : d236666 p = 1) (hb : d267636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236661 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127079 q = 1) (hb : d267631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127079, d267631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67148 q ha hb
    | true =>
      simp only [d127079, d267631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67119 q hb ha
  have h3 (q : Pattern) (ha : d236662 q = 1) (hb : d267632 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d236662, d267632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d236662, d267632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127086 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d236663 q = 1) (hb : d267633 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d236663, d267633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236663, d267633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d236664 q = 1) (hb : d267634 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d236664, d267634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236664, d267634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d236665 q = 1) (hb : d267635 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d236665, d267635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236665, d267635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d236666 q = 1) (hb : d267636 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d236666, d267636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236666, d267636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67435 (p : Pattern) (ha : d236672 p = 1) (hb : d267642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d126968 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236627 q = 1) (hb : d266350 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d236627, d266350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67431 q ha hb
    | true =>
      simp only [d236627, d266350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67432 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127035 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d236628 q = 1) (hb : d266351 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d236628, d266351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236628, d266351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d236629 q = 1) (hb : d267623 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236629, d267623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236629, d267623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d236630 q = 1) (hb : d267624 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236630, d267624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236630, d267624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d236634 q = 1) (hb : d267626 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d236634, d267626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d236634, d267626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67433 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d236635 q = 1) (hb : d267627 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d236635, d267627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d236635, d267627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d236636 q = 1) (hb : d267628 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236636, d267628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d236636, d267628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d236637 q = 1) (hb : d267629 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236637, d267629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d236637, d267629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d236638 q = 1) (hb : d267630 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d236638, d267630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d236638, d267630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d236667 q = 1) (hb : d267637 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d236667, d267637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d236667, d267637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67434 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d236668 q = 1) (hb : d267638 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d236668, d267638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d236668, d267638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d236669 q = 1) (hb : d267639 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236669, d267639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d236669, d267639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d236670 q = 1) (hb : d267640 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236670, d267640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d236670, d267640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d236671 q = 1) (hb : d267641 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d236671, d267641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d236671, d267641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d236672 q = 1) (hb : d267642 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d236672, d267642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d236672, d267642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro67436 (p : Pattern) (ha : d236678 p = 1) (hb : d267648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236673 q = 1) (hb : d267643 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d236673, d267643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236673, d267643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67435 q ha hb
  have h2 (q : Pattern) (ha : d236674 q = 1) (hb : d267644 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d236674, d267644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236674, d267644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d236675 q = 1) (hb : d267645 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d236675, d267645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236675, d267645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d236676 q = 1) (hb : d267646 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d236676, d267646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236676, d267646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d236677 q = 1) (hb : d267647 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d236677, d267647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236677, d267647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d236678 q = 1) (hb : d267648 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d236678, d267648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236678, d267648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67437 (p : Pattern) (ha : d236775 p = 1) (hb : d266529 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236717 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d236723 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d236764 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d236694 q = 1) (hb : d266524 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d236694, d266524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67168 q ha hb
    | true =>
      simp only [d236694, d266524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67158 q ha hb
  have h5 (q : Pattern) (ha : d236765 q = 1) (hb : d266525 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d236765, d266525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d236765, d266525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d236771 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d236772 q = 1) (hb : d266526 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d236772, d266526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d236772, d266526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d236773 q = 1) (hb : d266527 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d236773, d266527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d236773, d266527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d236774 q = 1) (hb : d266528 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d236774, d266528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d236774, d266528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d236775 q = 1) (hb : d266529 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d236775, d266529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236775, d266529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro67438 (p : Pattern) (ha : d236794 p = 1) (hb : d266539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236717 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d236764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d236694 q = 1) (hb : d266524 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d236694, d266524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67168 q ha hb
    | true =>
      simp only [d236694, d266524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67158 q ha hb
  have h4 (q : Pattern) (ha : d236765 q = 1) (hb : d266525 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d236765, d266525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d236765, d266525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d236771 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d236772 q = 1) (hb : d266526 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d236772, d266526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d236772, d266526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d236773 q = 1) (hb : d266527 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d236773, d266527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d236773, d266527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d236774 q = 1) (hb : d266528 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d236774, d266528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236774, d266528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d236780 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d236784 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d236786 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d236703 q = 1) (hb : d266534 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d236703, d266534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67170 q ha hb
    | true =>
      simp only [d236703, d266534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67159 q ha hb
  have h13 (q : Pattern) (ha : d236787 q = 1) (hb : d266535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d236787, d266535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d236787, d266535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d236790 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d236791 q = 1) (hb : d266536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d236791, d266536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d236791, d266536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d236792 q = 1) (hb : d266537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d236792, d266537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d236792, d266537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d236793 q = 1) (hb : d266538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d236793, d266538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d236793, d266538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d236794 q = 1) (hb : d266539 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d236794, d266539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d236794, d266539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro67439 (p : Pattern) (ha : d236803 p = 1) (hb : d267652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236786 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d236703 q = 1) (hb : d266534 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d236703, d266534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67170 q ha hb
    | true =>
      simp only [d236703, d266534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67159 q ha hb
  have h3 (q : Pattern) (ha : d236787 q = 1) (hb : d266535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d236787, d266535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d236787, d266535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d236790 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d236791 q = 1) (hb : d266536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d236791, d266536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236791, d266536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d236801 q = 1) (hb : d266537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d236801, d266537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236801, d266537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d236802 q = 1) (hb : d266538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d236802, d266538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236802, d266538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d236803 q = 1) (hb : d267652 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d236803, d267652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236803, d267652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67440 (p : Pattern) (ha : d236861 p = 1) (hb : d267663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236849 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d236850 q = 1) (hb : d267658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d236850, d267658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67200 q ha hb
    | true =>
      simp only [d236850, d267658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67164 q ha hb
  have h3 (q : Pattern) (ha : d236851 q = 1) (hb : d267659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d236851, d267659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d236851, d267659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d236857 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d236858 q = 1) (hb : d267660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d236858, d267660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236858, d267660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d236859 q = 1) (hb : d267661 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d236859, d267661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236859, d267661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d236860 q = 1) (hb : d267662 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d236860, d267662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236860, d267662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d236861 q = 1) (hb : d267663 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d236861, d267663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236861, d267663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67441 (p : Pattern) (ha : d236867 p = 1) (hb : d267669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236711 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236795 q = 1) (hb : d266540 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d236795, d266540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67437 q ha hb
    | true =>
      simp only [d236795, d266540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67438 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d236797 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d236798 q = 1) (hb : d266541 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d236798, d266541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d236798, d266541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d236799 q = 1) (hb : d267650 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236799, d267650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d236799, d267650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d236800 q = 1) (hb : d267651 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236800, d267651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236800, d267651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d236804 q = 1) (hb : d267653 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d236804, d267653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d236804, d267653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67439 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d236805 q = 1) (hb : d267654 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d236805, d267654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d236805, d267654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d236806 q = 1) (hb : d267655 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236806, d267655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d236806, d267655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d236807 q = 1) (hb : d267656 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236807, d267656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d236807, d267656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d236808 q = 1) (hb : d267657 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d236808, d267657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d236808, d267657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d236862 q = 1) (hb : d267664 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d236862, d267664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d236862, d267664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67440 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d236863 q = 1) (hb : d267665 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d236863, d267665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d236863, d267665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d236864 q = 1) (hb : d267666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d236864, d267666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d236864, d267666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d236865 q = 1) (hb : d267667 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d236865, d267667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d236865, d267667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d236866 q = 1) (hb : d267668 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d236866, d267668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d236866, d267668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d236867 q = 1) (hb : d267669 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d236867, d267669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d236867, d267669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro67442 (p : Pattern) (ha : d236873 p = 1) (hb : d267675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236868 q = 1) (hb : d267670 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d236868, d267670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236868, d267670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67441 q ha hb
  have h2 (q : Pattern) (ha : d236869 q = 1) (hb : d267671 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d236869, d267671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236869, d267671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d236870 q = 1) (hb : d267672 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d236870, d267672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236870, d267672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d236871 q = 1) (hb : d267673 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d236871, d267673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236871, d267673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d236872 q = 1) (hb : d267674 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d236872, d267674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236872, d267674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d236873 q = 1) (hb : d267675 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d236873, d267675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d236873, d267675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67443 (p : Pattern) (ha : d237017 p = 1) (hb : d266774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236956 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d236965 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d236997 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d236930 q = 1) (hb : d266769 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d236930, d266769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67213 q ha hb
    | true =>
      simp only [d236930, d266769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67214 q ha hb
  have h5 (q : Pattern) (ha : d236998 q = 1) (hb : d266770 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d236998, d266770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d236998, d266770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d237013 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d237014 q = 1) (hb : d266771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237014, d266771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237014, d266771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d237015 q = 1) (hb : d266772 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237015, d266772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d237015, d266772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237016 q = 1) (hb : d266773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237016, d266773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237016, d266773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237017 q = 1) (hb : d266774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237017, d266774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237017, d266774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro67444 (p : Pattern) (ha : d237038 p = 1) (hb : d266784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236956 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d236965 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d236997 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d236930 q = 1) (hb : d266769 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d236930, d266769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67213 q ha hb
    | true =>
      simp only [d236930, d266769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67214 q ha hb
  have h4 (q : Pattern) (ha : d236998 q = 1) (hb : d266770 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d236998, d266770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d236998, d266770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d237013 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d237014 q = 1) (hb : d266771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237014, d266771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237014, d266771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d237015 q = 1) (hb : d266772 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237015, d266772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237015, d266772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237016 q = 1) (hb : d266773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237016, d266773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237016, d266773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d237023 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d237028 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d237030 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d236940 q = 1) (hb : d266779 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d236940, d266779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67216 q ha hb
    | true =>
      simp only [d236940, d266779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67217 q ha hb
  have h13 (q : Pattern) (ha : d237031 q = 1) (hb : d266780 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237031, d266780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d237031, d266780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d237034 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d237035 q = 1) (hb : d266781 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237035, d266781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237035, d266781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d237036 q = 1) (hb : d266782 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237036, d266782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d237036, d266782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237037 q = 1) (hb : d266783 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237037, d266783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d237037, d266783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d237038 q = 1) (hb : d266784 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237038, d266784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237038, d266784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro67445 (p : Pattern) (ha : d237058 p = 1) (hb : d267680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237030 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d236940 q = 1) (hb : d266779 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d236940, d266779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67216 q ha hb
    | true =>
      simp only [d236940, d266779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67217 q ha hb
  have h3 (q : Pattern) (ha : d237031 q = 1) (hb : d266780 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237031, d266780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237031, d266780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d237034 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237035 q = 1) (hb : d266781 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237035, d266781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237035, d266781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237056 q = 1) (hb : d266782 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237056, d266782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237056, d266782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237057 q = 1) (hb : d266783 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237057, d266783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237057, d266783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237058 q = 1) (hb : d267680 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237058, d267680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237058, d267680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67446 (p : Pattern) (ha : d237157 p = 1) (hb : d267691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237132 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d237137 q = 1) (hb : d267686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237137, d267686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67253 q ha hb
    | true =>
      simp only [d237137, d267686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67258 q ha hb
  have h3 (q : Pattern) (ha : d237138 q = 1) (hb : d267687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237138, d267687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237138, d267687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d237153 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237154 q = 1) (hb : d267688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237154, d267688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237154, d267688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237155 q = 1) (hb : d267689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237155, d267689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237155, d267689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237156 q = 1) (hb : d267690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237156, d267690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237156, d267690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237157 q = 1) (hb : d267691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237157, d267691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237157, d267691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67447 (p : Pattern) (ha : d237170 p = 1) (hb : d267697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236948 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237039 q = 1) (hb : d266785 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237039, d266785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67443 q ha hb
    | true =>
      simp only [d237039, d266785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67444 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237052 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d237053 q = 1) (hb : d266786 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237053, d266786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237053, d266786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237054 q = 1) (hb : d267678 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237054, d267678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237054, d267678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237055 q = 1) (hb : d267679 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237055, d267679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237055, d267679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237059 q = 1) (hb : d267681 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237059, d267681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d237059, d267681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67445 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d237061 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d237062 q = 1) (hb : d267682 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237062, d267682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237062, d267682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d237063 q = 1) (hb : d267683 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237063, d267683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237063, d267683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d237064 q = 1) (hb : d267684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237064, d267684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237064, d267684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d237065 q = 1) (hb : d267685 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237065, d267685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237065, d267685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237158 q = 1) (hb : d267692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237158, d267692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d237158, d267692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67446 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d237165 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d237166 q = 1) (hb : d267693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237166, d267693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237166, d267693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d237167 q = 1) (hb : d267694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237167, d267694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237167, d267694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d237168 q = 1) (hb : d267695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237168, d267695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237168, d267695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d237169 q = 1) (hb : d267696 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237169, d267696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d237169, d267696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d237170 q = 1) (hb : d267697 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d237170, d267697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237170, d267697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro67448 (p : Pattern) (ha : d237176 p = 1) (hb : d267703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237171 q = 1) (hb : d267698 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d237171, d267698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237171, d267698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67447 q ha hb
  have h2 (q : Pattern) (ha : d237172 q = 1) (hb : d267699 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d237172, d267699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237172, d267699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237173 q = 1) (hb : d267700 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d237173, d267700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237173, d267700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237174 q = 1) (hb : d267701 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d237174, d267701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237174, d267701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237175 q = 1) (hb : d267702 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d237175, d267702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237175, d267702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237176 q = 1) (hb : d267703 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d237176, d267703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237176, d267703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67449 (p : Pattern) (ha : d237376 p = 1) (hb : d267067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237302 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d237341 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d237276 q = 1) (hb : d267062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237276, d267062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67274 q ha hb
    | true =>
      simp only [d237276, d267062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67275 q ha hb
  have h5 (q : Pattern) (ha : d237342 q = 1) (hb : d267063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237342, d267063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d237342, d267063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d237372 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d237373 q = 1) (hb : d267064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237373, d267064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237373, d267064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d237374 q = 1) (hb : d267065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237374, d267065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d237374, d267065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237375 q = 1) (hb : d267066 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237375, d267066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237375, d267066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237376 q = 1) (hb : d267067 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237376, d267067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237376, d267067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro67450 (p : Pattern) (ha : d237397 p = 1) (hb : d267077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d237302 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237311 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237341 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d237276 q = 1) (hb : d267062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237276, d267062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67274 q ha hb
    | true =>
      simp only [d237276, d267062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67275 q ha hb
  have h4 (q : Pattern) (ha : d237342 q = 1) (hb : d267063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237342, d267063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d237342, d267063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d237372 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d237373 q = 1) (hb : d267064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237373, d267064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237373, d267064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d237374 q = 1) (hb : d267065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237374, d267065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237374, d267065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237375 q = 1) (hb : d267066 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237375, d267066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237375, d267066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d237382 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d237387 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d237389 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d237286 q = 1) (hb : d267072 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237286, d267072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67277 q ha hb
    | true =>
      simp only [d237286, d267072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67278 q ha hb
  have h13 (q : Pattern) (ha : d237390 q = 1) (hb : d267073 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237390, d267073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d237390, d267073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d237393 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d237394 q = 1) (hb : d267074 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237394, d267074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237394, d267074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d237395 q = 1) (hb : d267075 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237395, d267075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d237395, d267075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237396 q = 1) (hb : d267076 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237396, d267076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d237396, d267076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d237397 q = 1) (hb : d267077 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237397, d267077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237397, d267077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro67451 (p : Pattern) (ha : d237417 p = 1) (hb : d267709 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237389 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d237286 q = 1) (hb : d267072 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237286, d267072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67277 q ha hb
    | true =>
      simp only [d237286, d267072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67278 q ha hb
  have h3 (q : Pattern) (ha : d237390 q = 1) (hb : d267073 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237390, d267073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237390, d267073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d237393 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237394 q = 1) (hb : d267074 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237394, d267074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237394, d267074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237415 q = 1) (hb : d267075 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237415, d267075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237415, d267075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237416 q = 1) (hb : d267076 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237416, d267076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237416, d267076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237417 q = 1) (hb : d267709 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237417, d267709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237417, d267709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67452 (p : Pattern) (ha : d237545 p = 1) (hb : d267720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237509 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d237514 q = 1) (hb : d267715 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237514, d267715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67317 q ha hb
    | true =>
      simp only [d237514, d267715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67323 q ha hb
  have h3 (q : Pattern) (ha : d237515 q = 1) (hb : d267716 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237515, d267716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237515, d267716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d237541 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237542 q = 1) (hb : d267717 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237542, d267717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237542, d267717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237543 q = 1) (hb : d267718 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237543, d267718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237543, d267718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237544 q = 1) (hb : d267719 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237544, d267719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237544, d267719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237545 q = 1) (hb : d267720 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237545, d267720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237545, d267720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67453 (p : Pattern) (ha : d237558 p = 1) (hb : d267726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d237294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237398 q = 1) (hb : d267078 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237398, d267078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67449 q ha hb
    | true =>
      simp only [d237398, d267078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67450 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237411 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d237412 q = 1) (hb : d267079 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237412, d267079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237412, d267079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237413 q = 1) (hb : d267707 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237413, d267707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237413, d267707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237414 q = 1) (hb : d267708 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237414, d267708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237414, d267708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237418 q = 1) (hb : d267710 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237418, d267710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d237418, d267710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67451 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d237420 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d237421 q = 1) (hb : d267711 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237421, d267711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237421, d267711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d237422 q = 1) (hb : d267712 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237422, d267712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237422, d267712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d237423 q = 1) (hb : d267713 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237423, d267713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237423, d267713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d237424 q = 1) (hb : d267714 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237424, d267714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237424, d267714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237546 q = 1) (hb : d267721 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237546, d267721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d237546, d267721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67452 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d237553 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d237554 q = 1) (hb : d267722 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237554, d267722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237554, d267722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d237555 q = 1) (hb : d267723 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237555, d267723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237555, d267723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d237556 q = 1) (hb : d267724 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237556, d267724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237556, d267724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d237557 q = 1) (hb : d267725 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237557, d267725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d237557, d267725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d237558 q = 1) (hb : d267726 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d237558, d267726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237558, d267726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro67454 (p : Pattern) (ha : d237564 p = 1) (hb : d267732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237559 q = 1) (hb : d267727 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d237559, d267727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237559, d267727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67453 q ha hb
  have h2 (q : Pattern) (ha : d237560 q = 1) (hb : d267728 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d237560, d267728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237560, d267728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237561 q = 1) (hb : d267729 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d237561, d267729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237561, d267729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237562 q = 1) (hb : d267730 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d237562, d267730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237562, d267730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237563 q = 1) (hb : d267731 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d237563, d267731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237563, d267731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237564 q = 1) (hb : d267732 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d237564, d267732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237564, d267732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67455 (p : Pattern) (ha : d237753 p = 1) (hb : d267358 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237680 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237689 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d237713 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d237654 q = 1) (hb : d267353 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237654, d267353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67338 q ha hb
    | true =>
      simp only [d237654, d267353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67339 q ha hb
  have h5 (q : Pattern) (ha : d237714 q = 1) (hb : d267354 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237714, d267354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d237714, d267354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d237749 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d237750 q = 1) (hb : d267355 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237750, d267355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237750, d267355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d237751 q = 1) (hb : d267356 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237751, d267356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d237751, d267356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237752 q = 1) (hb : d267357 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237752, d267357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237752, d267357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237753 q = 1) (hb : d267358 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237753, d267358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237753, d267358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro67456 (p : Pattern) (ha : d237774 p = 1) (hb : d267368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d237680 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237689 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237713 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d237654 q = 1) (hb : d267353 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237654, d267353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67338 q ha hb
    | true =>
      simp only [d237654, d267353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67339 q ha hb
  have h4 (q : Pattern) (ha : d237714 q = 1) (hb : d267354 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237714, d267354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d237714, d267354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d237749 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d237750 q = 1) (hb : d267355 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237750, d267355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237750, d267355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d237751 q = 1) (hb : d267356 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237751, d267356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237751, d267356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237752 q = 1) (hb : d267357 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237752, d267357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237752, d267357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d237759 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d237764 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d237766 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d237664 q = 1) (hb : d267363 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237664, d267363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67341 q ha hb
    | true =>
      simp only [d237664, d267363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67342 q ha hb
  have h13 (q : Pattern) (ha : d237767 q = 1) (hb : d267364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237767, d267364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d237767, d267364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d237770 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d237771 q = 1) (hb : d267365 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237771, d267365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237771, d267365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d237772 q = 1) (hb : d267366 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237772, d267366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d237772, d267366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d237773 q = 1) (hb : d267367 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237773, d267367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d237773, d267367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d237774 q = 1) (hb : d267368 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237774, d267368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237774, d267368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro67457 (p : Pattern) (ha : d237794 p = 1) (hb : d267739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d237664 q = 1) (hb : d267363 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237664, d267363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67341 q ha hb
    | true =>
      simp only [d237664, d267363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67342 q ha hb
  have h3 (q : Pattern) (ha : d237767 q = 1) (hb : d267364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237767, d267364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237767, d267364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d237770 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237771 q = 1) (hb : d267365 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237771, d267365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237771, d267365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237792 q = 1) (hb : d267366 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237792, d267366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237792, d267366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237793 q = 1) (hb : d267367 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237793, d267367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237793, d267367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237794 q = 1) (hb : d267739 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237794, d267739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237794, d267739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67458 (p : Pattern) (ha : d237913 p = 1) (hb : d267750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d237877 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d237882 q = 1) (hb : d267745 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d237882, d267745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67379 q ha hb
    | true =>
      simp only [d237882, d267745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67385 q ha hb
  have h3 (q : Pattern) (ha : d237883 q = 1) (hb : d267746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d237883, d267746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237883, d267746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d237909 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237910 q = 1) (hb : d267747 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d237910, d267747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237910, d267747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237911 q = 1) (hb : d267748 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d237911, d267748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237911, d267748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237912 q = 1) (hb : d267749 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d237912, d267749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237912, d267749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d237913 q = 1) (hb : d267750 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d237913, d267750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237913, d267750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67459 (p : Pattern) (ha : d237926 p = 1) (hb : d267756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d237672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237775 q = 1) (hb : d267369 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237775, d267369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67455 q ha hb
    | true =>
      simp only [d237775, d267369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67456 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d237788 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d237789 q = 1) (hb : d267370 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237789, d267370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237789, d267370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d237790 q = 1) (hb : d267737 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237790, d267737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237790, d267737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d237791 q = 1) (hb : d267738 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237791, d267738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237791, d267738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237795 q = 1) (hb : d267740 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237795, d267740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d237795, d267740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67457 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d237797 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d237798 q = 1) (hb : d267741 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237798, d267741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d237798, d267741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d237799 q = 1) (hb : d267742 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237799, d267742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d237799, d267742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d237800 q = 1) (hb : d267743 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237800, d267743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237800, d267743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d237801 q = 1) (hb : d267744 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237801, d267744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237801, d267744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237914 q = 1) (hb : d267751 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d237914, d267751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d237914, d267751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67458 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d237921 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d237922 q = 1) (hb : d267752 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d237922, d267752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d237922, d267752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d237923 q = 1) (hb : d267753 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d237923, d267753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237923, d267753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d237924 q = 1) (hb : d267754 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d237924, d267754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d237924, d267754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d237925 q = 1) (hb : d267755 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d237925, d267755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d237925, d267755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d237926 q = 1) (hb : d267756 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d237926, d267756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d237926, d267756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro67460 (p : Pattern) (ha : d237932 p = 1) (hb : d267762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237927 q = 1) (hb : d267757 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d237927, d267757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237927, d267757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67459 q ha hb
  have h2 (q : Pattern) (ha : d237928 q = 1) (hb : d267758 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d237928, d267758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237928, d267758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d237929 q = 1) (hb : d267759 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d237929, d267759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237929, d267759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237930 q = 1) (hb : d267760 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d237930, d267760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237930, d267760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d237931 q = 1) (hb : d267761 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d237931, d267761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237931, d267761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237932 q = 1) (hb : d267762 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d237932, d267762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d237932, d267762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67461 (p : Pattern) (ha : d237938 p = 1) (hb : d267768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d236679 q = 1) (hb : d267649 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d236679, d267649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67430 q ha hb
    | true =>
      simp only [d236679, d267649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67436 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d236874 q = 1) (hb : d267676 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d236874, d267676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d236874, d267676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67442 q ha hb
  have h3 (q : Pattern) (ha : d236875 q = 1) (hb : d267677 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d236875, d267677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d236875, d267677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d237177 q = 1) (hb : d267704 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d237177, d267704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237177, d267704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67448 q ha hb
  have h5 (q : Pattern) (ha : d237178 q = 1) (hb : d267705 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d237178, d267705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237178, d267705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d237179 q = 1) (hb : d267706 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d237179, d267706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237179, d267706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d237565 q = 1) (hb : d267733 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d237565, d267733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237565, d267733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67454 q ha hb
  have h8 (q : Pattern) (ha : d237566 q = 1) (hb : d267734 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d237566, d267734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237566, d267734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237567 q = 1) (hb : d267735 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d237567, d267735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237567, d267735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d237568 q = 1) (hb : d267736 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d237568, d267736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d237568, d267736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d237933 q = 1) (hb : d267763 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d237933, d267763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237933, d267763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67460 q ha hb
  have h12 (q : Pattern) (ha : d237934 q = 1) (hb : d267764 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d237934, d267764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237934, d267764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d237935 q = 1) (hb : d267765 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d237935, d267765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237935, d267765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d237936 q = 1) (hb : d267766 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d237936, d267766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d237936, d267766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d237937 q = 1) (hb : d267767 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d237937, d267767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d237937, d267767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d237938 q = 1) (hb : d267768 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d237938, d267768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d237938, d267768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro67462 (p : Pattern) (ha : d237944 p = 1) (hb : d267774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237939 q = 1) (hb : d267769 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d237939, d267769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67461 q ha hb
    | true =>
      simp only [d237939, d267769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237940 q = 1) (hb : d267770 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d237940, d267770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237940, d267770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237941 q = 1) (hb : d267771 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d237941, d267771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237941, d267771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237942 q = 1) (hb : d267772 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d237942, d267772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237942, d267772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237943 q = 1) (hb : d267773 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d237943, d267773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237943, d267773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237944 q = 1) (hb : d267774 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d237944, d267774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237944, d267774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67463 (p : Pattern) (ha : d237950 p = 1) (hb : d267780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237945 q = 1) (hb : d267775 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d237945, d267775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67462 q ha hb
    | true =>
      simp only [d237945, d267775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237946 q = 1) (hb : d267776 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d237946, d267776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237946, d267776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237947 q = 1) (hb : d267777 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d237947, d267777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237947, d267777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237948 q = 1) (hb : d267778 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d237948, d267778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237948, d267778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237949 q = 1) (hb : d267779 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d237949, d267779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237949, d267779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237950 q = 1) (hb : d267780 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d237950, d267780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237950, d267780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67464 (p : Pattern) (ha : d237956 p = 1) (hb : d267786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237951 q = 1) (hb : d267781 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d237951, d267781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67463 q ha hb
    | true =>
      simp only [d237951, d267781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237952 q = 1) (hb : d267782 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d237952, d267782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237952, d267782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237953 q = 1) (hb : d267783 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d237953, d267783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237953, d267783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237954 q = 1) (hb : d267784 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d237954, d267784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237954, d267784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237955 q = 1) (hb : d267785 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d237955, d267785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237955, d267785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237956 q = 1) (hb : d267786 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d237956, d267786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237956, d267786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67465 (p : Pattern) (ha : d237962 p = 1) (hb : d267792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237957 q = 1) (hb : d267787 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d237957, d267787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67464 q ha hb
    | true =>
      simp only [d237957, d267787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237958 q = 1) (hb : d267788 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d237958, d267788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237958, d267788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237959 q = 1) (hb : d267789 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d237959, d267789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237959, d267789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237960 q = 1) (hb : d267790 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d237960, d267790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237960, d267790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237961 q = 1) (hb : d267791 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d237961, d267791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237961, d267791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237962 q = 1) (hb : d267792 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d237962, d267792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237962, d267792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67466 (p : Pattern) (ha : d237968 p = 1) (hb : d267798 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237963 q = 1) (hb : d267793 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d237963, d267793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67465 q ha hb
    | true =>
      simp only [d237963, d267793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237964 q = 1) (hb : d267794 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d237964, d267794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237964, d267794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237965 q = 1) (hb : d267795 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d237965, d267795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237965, d267795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237966 q = 1) (hb : d267796 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d237966, d267796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237966, d267796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237967 q = 1) (hb : d267797 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d237967, d267797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237967, d267797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237968 q = 1) (hb : d267798 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d237968, d267798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237968, d267798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67467 (p : Pattern) (ha : d237974 p = 1) (hb : d267804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237969 q = 1) (hb : d267799 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d237969, d267799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67466 q ha hb
    | true =>
      simp only [d237969, d267799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237970 q = 1) (hb : d267800 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d237970, d267800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237970, d267800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237971 q = 1) (hb : d267801 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d237971, d267801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237971, d267801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237972 q = 1) (hb : d267802 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d237972, d267802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237972, d267802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237973 q = 1) (hb : d267803 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d237973, d267803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237973, d267803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237974 q = 1) (hb : d267804 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d237974, d267804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237974, d267804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67468 (p : Pattern) (ha : d237980 p = 1) (hb : d267810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d237975 q = 1) (hb : d267805 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d237975, d267805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67467 q ha hb
    | true =>
      simp only [d237975, d267805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d237976 q = 1) (hb : d267806 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d237976, d267806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d237976, d267806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d237977 q = 1) (hb : d267807 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d237977, d267807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d237977, d267807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d237978 q = 1) (hb : d267808 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d237978, d267808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d237978, d267808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d237979 q = 1) (hb : d267809 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d237979, d267809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d237979, d267809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d237980 q = 1) (hb : d267810 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d237980, d267810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d237980, d267810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro67469 (p : Pattern) (ha : d25187 p = 1) (hb : d128195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15979 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d25123 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25183 q = 1) (hb : d128191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25183, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25184 q = 1) (hb : d128192 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25184, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25185 q = 1) (hb : d128193 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25185, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25186 q = 1) (hb : d128194 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25186, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25187 q = 1) (hb : d128195 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25187, d128195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25187, d128195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro67470 (p : Pattern) (ha : d25194 p = 1) (hb : d128200 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15979 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d25123 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25183 q = 1) (hb : d128191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25183, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25184 q = 1) (hb : d128192 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25184, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25185 q = 1) (hb : d128193 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25185, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25186 q = 1) (hb : d128194 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25186, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d380 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d384 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d15986 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d25130 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d25190 q = 1) (hb : d128196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25190, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25190, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d25191 q = 1) (hb : d128197 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25191, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25191, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25192 q = 1) (hb : d128198 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25192, d128198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25192, d128198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25193 q = 1) (hb : d128199 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25193, d128199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25193, d128199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d25194 q = 1) (hb : d128200 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25194, d128200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25194, d128200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro67471 (p : Pattern) (ha : d128207 p = 1) (hb : d245682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15986 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25130 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d25190 q = 1) (hb : d128196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25190, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25190, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25191 q = 1) (hb : d128197 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25191, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25191, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25192 q = 1) (hb : d128205 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25192, d128205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25192, d128205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25193 q = 1) (hb : d128206 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25193, d128206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25193, d128206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128207 q = 1) (hb : d245682 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128207, d245682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128207, d245682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro67472 (p : Pattern) (ha : d128217 p = 1) (hb : d245692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16017 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d25166 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128213 q = 1) (hb : d245688 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128213, d245688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128213, d245688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5379 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128214 q = 1) (hb : d245689 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128214, d245689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128214, d245689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128215 q = 1) (hb : d245690 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128215, d245690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128215, d245690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128216 q = 1) (hb : d245691 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128216, d245691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128216, d245691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128217 q = 1) (hb : d245692 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128217, d245692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128217, d245692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67473 (p : Pattern) (ha : d128223 p = 1) (hb : d245698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25195 q = 1) (hb : d128201 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25195, d128201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67469 q ha hb
    | true =>
      simp only [d25195, d128201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67470 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d25196 q = 1) (hb : d128202 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25196, d128202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25196, d128202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128203 q = 1) (hb : d245680 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128203, d245680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128203, d245680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128204 q = 1) (hb : d245681 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128204, d245681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128204, d245681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128208 q = 1) (hb : d245683 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128208, d245683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128208, d245683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67471 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128209 q = 1) (hb : d245684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128209, d245684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128209, d245684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128210 q = 1) (hb : d245685 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128210, d245685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128210, d245685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128211 q = 1) (hb : d245686 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128211, d245686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128211, d245686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128212 q = 1) (hb : d245687 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128212, d245687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128212, d245687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128218 q = 1) (hb : d245693 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128218, d245693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128218, d245693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67472 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128219 q = 1) (hb : d245694 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128219, d245694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128219, d245694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128220 q = 1) (hb : d245695 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128220, d245695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128220, d245695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128221 q = 1) (hb : d245696 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128221, d245696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128221, d245696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128222 q = 1) (hb : d245697 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128222, d245697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128222, d245697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128223 q = 1) (hb : d245698 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128223, d245698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128223, d245698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro67474 (p : Pattern) (ha : d128229 p = 1) (hb : d245704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d53648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro376 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d53649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d53650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d53652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51657, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128224 q = 1) (hb : d245699 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128224, d245699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128224, d245699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67473 q ha hb
  have h8 (q : Pattern) (ha : d128225 q = 1) (hb : d245700 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128225, d245700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128225, d245700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128226 q = 1) (hb : d245701 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128226, d245701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128226, d245701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128227 q = 1) (hb : d245702 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128227, d245702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128227, d245702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128228 q = 1) (hb : d245703 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128228, d245703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128228, d245703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128229 q = 1) (hb : d245704 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128229, d245704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128229, d245704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro67475 (p : Pattern) (ha : d238875 p = 1) (hb : d266340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16066 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16072 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d28769 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d266335 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238871 q = 1) (hb : d266336 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238871, d266336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d238871, d266336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d16116 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d238872 q = 1) (hb : d266337 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238872, d266337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238872, d266337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d238873 q = 1) (hb : d266338 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238873, d266338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d238873, d266338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d238874 q = 1) (hb : d266339 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238874, d266339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238874, d266339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d238875 q = 1) (hb : d266340 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238875, d266340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238875, d266340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro67476 (p : Pattern) (ha : d238880 p = 1) (hb : d266349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16066 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16072 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d28769 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d266335 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d238871 q = 1) (hb : d266336 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238871, d266336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d238871, d266336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16116 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d238872 q = 1) (hb : d266337 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238872, d266337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238872, d266337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d238873 q = 1) (hb : d266338 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238873, d266338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238873, d266338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238874 q = 1) (hb : d266339 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238874, d266339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238874, d266339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16125 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d16129 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d28776 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d266344 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d238876 q = 1) (hb : d266345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238876, d266345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d238876, d266345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d16137 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d238877 q = 1) (hb : d266346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238877, d266346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d238877, d266346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d238878 q = 1) (hb : d266347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238878, d266347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d238878, d266347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d238879 q = 1) (hb : d266348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238879, d266348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d238879, d266348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d238880 q = 1) (hb : d266349 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238880, d266349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238880, d266349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro67477 (p : Pattern) (ha : d238887 p = 1) (hb : d267625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28776 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d266344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238876 q = 1) (hb : d266345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238876, d266345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238876, d266345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16137 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238877 q = 1) (hb : d266346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238877, d266346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238877, d266346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d238885 q = 1) (hb : d266347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238885, d266347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238885, d266347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238886 q = 1) (hb : d266348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238886, d266348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238886, d266348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238887 q = 1) (hb : d267625 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238887, d267625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238887, d267625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67478 (p : Pattern) (ha : d238897 p = 1) (hb : d267636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28816 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d267631 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238893 q = 1) (hb : d267632 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238893, d267632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238893, d267632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16209 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238894 q = 1) (hb : d267633 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238894, d267633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238894, d267633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d238895 q = 1) (hb : d267634 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238895, d267634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238895, d267634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238896 q = 1) (hb : d267635 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238896, d267635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238896, d267635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238897 q = 1) (hb : d267636 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238897, d267636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238897, d267636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67479 (p : Pattern) (ha : d238903 p = 1) (hb : d267642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16060 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238881 q = 1) (hb : d266350 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238881, d266350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67475 q ha hb
    | true =>
      simp only [d238881, d266350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67476 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16144 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238882 q = 1) (hb : d266351 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238882, d266351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238882, d266351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238883 q = 1) (hb : d267623 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238883, d267623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238883, d267623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238884 q = 1) (hb : d267624 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238884, d267624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238884, d267624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238888 q = 1) (hb : d267626 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238888, d267626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238888, d267626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67477 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d238889 q = 1) (hb : d267627 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238889, d267627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d238889, d267627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d238890 q = 1) (hb : d267628 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238890, d267628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238890, d267628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d238891 q = 1) (hb : d267629 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238891, d267629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d238891, d267629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d238892 q = 1) (hb : d267630 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238892, d267630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d238892, d267630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d238898 q = 1) (hb : d267637 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238898, d267637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238898, d267637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67478 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d238899 q = 1) (hb : d267638 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238899, d267638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d238899, d267638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d238900 q = 1) (hb : d267639 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238900, d267639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d238900, d267639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d238901 q = 1) (hb : d267640 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238901, d267640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d238901, d267640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d238902 q = 1) (hb : d267641 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238902, d267641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d238902, d267641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d238903 q = 1) (hb : d267642 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d238903, d267642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d238903, d267642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro67480 (p : Pattern) (ha : d238909 p = 1) (hb : d267648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238904 q = 1) (hb : d267643 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d238904, d267643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238904, d267643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67479 q ha hb
  have h2 (q : Pattern) (ha : d238905 q = 1) (hb : d267644 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d238905, d267644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238905, d267644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238906 q = 1) (hb : d267645 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d238906, d267645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238906, d267645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d238907 q = 1) (hb : d267646 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d238907, d267646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238907, d267646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d238908 q = 1) (hb : d267647 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d238908, d267647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238908, d267647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238909 q = 1) (hb : d267648 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d238909, d267648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238909, d267648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67481 (p : Pattern) (ha : d238915 p = 1) (hb : d266529 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28872 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d28878 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d28919 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d266524 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238911 q = 1) (hb : d266525 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238911, d266525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d238911, d266525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d28958 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d238912 q = 1) (hb : d266526 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238912, d266526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238912, d266526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d238913 q = 1) (hb : d266527 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238913, d266527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d238913, d266527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d238914 q = 1) (hb : d266528 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238914, d266528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238914, d266528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d238915 q = 1) (hb : d266529 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238915, d266529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238915, d266529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro67482 (p : Pattern) (ha : d238920 p = 1) (hb : d266539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d28872 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28878 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d28919 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d266524 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d238911 q = 1) (hb : d266525 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238911, d266525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d238911, d266525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d28958 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d238912 q = 1) (hb : d266526 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238912, d266526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238912, d266526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d238913 q = 1) (hb : d266527 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238913, d266527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238913, d266527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238914 q = 1) (hb : d266528 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238914, d266528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238914, d266528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d28967 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d28971 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d28973 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d266534 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d238916 q = 1) (hb : d266535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238916, d266535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d238916, d266535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d28979 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d238917 q = 1) (hb : d266536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238917, d266536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d238917, d266536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d238918 q = 1) (hb : d266537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238918, d266537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d238918, d266537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d238919 q = 1) (hb : d266538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238919, d266538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d238919, d266538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d238920 q = 1) (hb : d266539 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238920, d266539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238920, d266539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro67483 (p : Pattern) (ha : d238927 p = 1) (hb : d267652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28973 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d266534 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238916 q = 1) (hb : d266535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238916, d266535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238916, d266535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d28979 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238917 q = 1) (hb : d266536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238917, d266536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238917, d266536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d238925 q = 1) (hb : d266537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238925, d266537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238925, d266537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238926 q = 1) (hb : d266538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238926, d266538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238926, d266538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238927 q = 1) (hb : d267652 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238927, d267652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238927, d267652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67484 (p : Pattern) (ha : d238937 p = 1) (hb : d267663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29038 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d267658 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238933 q = 1) (hb : d267659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238933, d267659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238933, d267659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d29069 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238934 q = 1) (hb : d267660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238934, d267660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238934, d267660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d238935 q = 1) (hb : d267661 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238935, d267661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238935, d267661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238936 q = 1) (hb : d267662 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238936, d267662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238936, d267662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238937 q = 1) (hb : d267663 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238937, d267663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238937, d267663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67485 (p : Pattern) (ha : d238943 p = 1) (hb : d267669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d28866 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238921 q = 1) (hb : d266540 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238921, d266540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67481 q ha hb
    | true =>
      simp only [d238921, d266540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67482 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d28986 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238922 q = 1) (hb : d266541 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238922, d266541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238922, d266541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238923 q = 1) (hb : d267650 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238923, d267650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238923, d267650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238924 q = 1) (hb : d267651 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238924, d267651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238924, d267651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238928 q = 1) (hb : d267653 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238928, d267653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238928, d267653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67483 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d238929 q = 1) (hb : d267654 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238929, d267654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d238929, d267654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d238930 q = 1) (hb : d267655 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238930, d267655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238930, d267655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d238931 q = 1) (hb : d267656 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238931, d267656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d238931, d267656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d238932 q = 1) (hb : d267657 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238932, d267657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d238932, d267657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d238938 q = 1) (hb : d267664 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238938, d267664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238938, d267664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67484 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d238939 q = 1) (hb : d267665 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238939, d267665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d238939, d267665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d238940 q = 1) (hb : d267666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238940, d267666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d238940, d267666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d238941 q = 1) (hb : d267667 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238941, d267667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d238941, d267667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d238942 q = 1) (hb : d267668 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238942, d267668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d238942, d267668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d238943 q = 1) (hb : d267669 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d238943, d267669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d238943, d267669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro67486 (p : Pattern) (ha : d238949 p = 1) (hb : d267675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238944 q = 1) (hb : d267670 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d238944, d267670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238944, d267670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67485 q ha hb
  have h2 (q : Pattern) (ha : d238945 q = 1) (hb : d267671 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d238945, d267671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238945, d267671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238946 q = 1) (hb : d267672 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d238946, d267672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238946, d267672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d238947 q = 1) (hb : d267673 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d238947, d267673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238947, d267673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d238948 q = 1) (hb : d267674 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d238948, d267674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238948, d267674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238949 q = 1) (hb : d267675 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d238949, d267675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238949, d267675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67487 (p : Pattern) (ha : d238956 p = 1) (hb : d266774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29168 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d29177 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d29209 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d266769 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238952 q = 1) (hb : d266770 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238952, d266770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d238952, d266770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d29304 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d238953 q = 1) (hb : d266771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238953, d266771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238953, d266771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d238954 q = 1) (hb : d266772 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238954, d266772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d238954, d266772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d238955 q = 1) (hb : d266773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238955, d266773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238955, d266773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d238956 q = 1) (hb : d266774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238956, d266774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238956, d266774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro67488 (p : Pattern) (ha : d238961 p = 1) (hb : d266784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d29168 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29177 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d29209 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d266769 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d238952 q = 1) (hb : d266770 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238952, d266770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d238952, d266770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d29304 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d238953 q = 1) (hb : d266771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238953, d266771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238953, d266771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d238954 q = 1) (hb : d266772 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238954, d266772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238954, d266772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238955 q = 1) (hb : d266773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238955, d266773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238955, d266773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d29314 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d29319 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d29321 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d266779 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d238957 q = 1) (hb : d266780 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238957, d266780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d238957, d266780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d29328 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d238958 q = 1) (hb : d266781 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238958, d266781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d238958, d266781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d238959 q = 1) (hb : d266782 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238959, d266782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d238959, d266782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d238960 q = 1) (hb : d266783 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238960, d266783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d238960, d266783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d238961 q = 1) (hb : d266784 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238961, d266784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238961, d266784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro67489 (p : Pattern) (ha : d238968 p = 1) (hb : d267680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29321 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d266779 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238957 q = 1) (hb : d266780 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238957, d266780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238957, d266780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d29328 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238958 q = 1) (hb : d266781 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238958, d266781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238958, d266781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d238966 q = 1) (hb : d266782 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238966, d266782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238966, d266782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238967 q = 1) (hb : d266783 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238967, d266783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238967, d266783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238968 q = 1) (hb : d267680 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238968, d267680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238968, d267680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67490 (p : Pattern) (ha : d238978 p = 1) (hb : d267691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29426 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d267686 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238974 q = 1) (hb : d267687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238974, d267687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238974, d267687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d29496 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238975 q = 1) (hb : d267688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238975, d267688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238975, d267688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d238976 q = 1) (hb : d267689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238976, d267689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238976, d267689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238977 q = 1) (hb : d267690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238977, d267690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238977, d267690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238978 q = 1) (hb : d267691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238978, d267691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238978, d267691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67491 (p : Pattern) (ha : d238984 p = 1) (hb : d267697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d29160 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238962 q = 1) (hb : d266785 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238962, d266785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67487 q ha hb
    | true =>
      simp only [d238962, d266785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67488 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d29346 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238963 q = 1) (hb : d266786 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238963, d266786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238963, d266786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238964 q = 1) (hb : d267678 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238964, d267678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238964, d267678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238965 q = 1) (hb : d267679 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238965, d267679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238965, d267679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238969 q = 1) (hb : d267681 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238969, d267681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238969, d267681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67489 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d29355 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d238970 q = 1) (hb : d267682 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238970, d267682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d238970, d267682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d238971 q = 1) (hb : d267683 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238971, d267683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238971, d267683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d238972 q = 1) (hb : d267684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238972, d267684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d238972, d267684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d238973 q = 1) (hb : d267685 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238973, d267685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d238973, d267685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d238979 q = 1) (hb : d267692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238979, d267692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238979, d267692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67490 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d29512 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d238980 q = 1) (hb : d267693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238980, d267693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d238980, d267693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d238981 q = 1) (hb : d267694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238981, d267694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d238981, d267694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d238982 q = 1) (hb : d267695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238982, d267695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d238982, d267695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d238983 q = 1) (hb : d267696 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238983, d267696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d238983, d267696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d238984 q = 1) (hb : d267697 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d238984, d267697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d238984, d267697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro67492 (p : Pattern) (ha : d238990 p = 1) (hb : d267703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238985 q = 1) (hb : d267698 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d238985, d267698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238985, d267698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67491 q ha hb
  have h2 (q : Pattern) (ha : d238986 q = 1) (hb : d267699 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d238986, d267699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238986, d267699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238987 q = 1) (hb : d267700 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d238987, d267700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238987, d267700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d238988 q = 1) (hb : d267701 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d238988, d267701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238988, d267701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d238989 q = 1) (hb : d267702 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d238989, d267702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238989, d267702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238990 q = 1) (hb : d267703 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d238990, d267703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238990, d267703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67493 (p : Pattern) (ha : d238998 p = 1) (hb : d267067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29649 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d29658 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d29688 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d267062 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238994 q = 1) (hb : d267063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238994, d267063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d238994, d267063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d29816 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d238995 q = 1) (hb : d267064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238995, d267064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238995, d267064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d238996 q = 1) (hb : d267065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238996, d267065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d238996, d267065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d238997 q = 1) (hb : d267066 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238997, d267066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238997, d267066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d238998 q = 1) (hb : d267067 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238998, d267067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238998, d267067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro67494 (p : Pattern) (ha : d239003 p = 1) (hb : d267077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d29649 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29658 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d29688 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d267062 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d238994 q = 1) (hb : d267063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238994, d267063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d238994, d267063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d29816 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d238995 q = 1) (hb : d267064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238995, d267064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238995, d267064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d238996 q = 1) (hb : d267065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238996, d267065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238996, d267065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238997 q = 1) (hb : d267066 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238997, d267066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238997, d267066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d29826 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d29831 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d29833 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d267072 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d238999 q = 1) (hb : d267073 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238999, d267073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d238999, d267073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d29840 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d239000 q = 1) (hb : d267074 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d239000, d267074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d239000, d267074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d239001 q = 1) (hb : d267075 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d239001, d267075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d239001, d267075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d239002 q = 1) (hb : d267076 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d239002, d267076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d239002, d267076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d239003 q = 1) (hb : d267077 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d239003, d267077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d239003, d267077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro67495 (p : Pattern) (ha : d239010 p = 1) (hb : d267709 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29833 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d267072 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238999 q = 1) (hb : d267073 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238999, d267073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238999, d267073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d29840 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d239000 q = 1) (hb : d267074 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d239000, d267074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239000, d267074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d239008 q = 1) (hb : d267075 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d239008, d267075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239008, d267075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d239009 q = 1) (hb : d267076 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d239009, d267076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239009, d267076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d239010 q = 1) (hb : d267709 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d239010, d267709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239010, d267709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67496 (p : Pattern) (ha : d239020 p = 1) (hb : d267720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29956 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d267715 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d239016 q = 1) (hb : d267716 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d239016, d267716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d239016, d267716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d30045 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d239017 q = 1) (hb : d267717 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d239017, d267717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239017, d267717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d239018 q = 1) (hb : d267718 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d239018, d267718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239018, d267718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d239019 q = 1) (hb : d267719 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d239019, d267719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239019, d267719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d239020 q = 1) (hb : d267720 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d239020, d267720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239020, d267720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro67497 (p : Pattern) (ha : d239026 p = 1) (hb : d267726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d29641 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239004 q = 1) (hb : d267078 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d239004, d267078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67493 q ha hb
    | true =>
      simp only [d239004, d267078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67494 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d29858 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d239005 q = 1) (hb : d267079 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d239005, d267079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239005, d267079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d239006 q = 1) (hb : d267707 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d239006, d267707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239006, d267707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d239007 q = 1) (hb : d267708 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d239007, d267708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d239007, d267708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d239011 q = 1) (hb : d267710 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d239011, d267710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239011, d267710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67495 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d29867 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d239012 q = 1) (hb : d267711 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d239012, d267711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d239012, d267711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d239013 q = 1) (hb : d267712 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d239013, d267712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d239013, d267712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d239014 q = 1) (hb : d267713 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d239014, d267713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d239014, d267713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d239015 q = 1) (hb : d267714 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d239015, d267714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d239015, d267714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d239021 q = 1) (hb : d267721 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d239021, d267721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239021, d267721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67496 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d30061 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d239022 q = 1) (hb : d267722 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d239022, d267722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d239022, d267722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d239023 q = 1) (hb : d267723 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d239023, d267723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d239023, d267723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d239024 q = 1) (hb : d267724 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d239024, d267724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d239024, d267724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d239025 q = 1) (hb : d267725 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d239025, d267725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d239025, d267725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d239026 q = 1) (hb : d267726 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d239026, d267726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d239026, d267726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro67498 (p : Pattern) (ha : d239032 p = 1) (hb : d267732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239027 q = 1) (hb : d267727 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d239027, d267727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239027, d267727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67497 q ha hb
  have h2 (q : Pattern) (ha : d239028 q = 1) (hb : d267728 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d239028, d267728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239028, d267728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d239029 q = 1) (hb : d267729 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d239029, d267729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239029, d267729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d239030 q = 1) (hb : d267730 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d239030, d267730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239030, d267730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d239031 q = 1) (hb : d267731 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d239031, d267731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239031, d267731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d239032 q = 1) (hb : d267732 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d239032, d267732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239032, d267732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro67499 (p : Pattern) (ha : d239041 p = 1) (hb : d267358 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30188 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30197 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d30221 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d267353 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d239037 q = 1) (hb : d267354 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d239037, d267354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d239037, d267354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d30343 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d239038 q = 1) (hb : d267355 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d239038, d267355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d239038, d267355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d239039 q = 1) (hb : d267356 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d239039, d267356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d239039, d267356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d239040 q = 1) (hb : d267357 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d239040, d267357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d239040, d267357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d239041 q = 1) (hb : d267358 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d239041, d267358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239041, d267358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
end NetHack.Soko22Hazard87
