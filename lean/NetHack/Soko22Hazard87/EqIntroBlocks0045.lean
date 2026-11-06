import NetHack.Soko22Hazard87.EqIntroBlocks0044
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro11250 (p : Pattern) (selected : d132905 p = 0) : d134168 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132889 q = 0) : d134154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132889, d134154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11246 q selected
    | true =>
      simp only [d132889, d134154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11228 q selected
  have h2 (q : Pattern) (selected : d132891 q = 0) : d134062 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132891, d134062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11247 q selected
    | true =>
      simp only [d132891, d134062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d132892 q = 0) : d134155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132892, d134155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d132892, d134155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d132788 q = 0) : d134062 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132788, d134062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11228 q selected
    | true =>
      simp only [d132788, d134062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d132789 q = 0) : d134063 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132789, d134063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d132789, d134063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d132893 q = 0) : d134156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132893, d134156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d132893, d134156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d132903 q = 0) : d134166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132903, d134166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132903, d134166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d132904 q = 0) : d134167 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132904, d134167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132904, d134167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d132905 q = 0) : d134168 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132905, d134168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132905, d134168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11251 (p : Pattern) (selected : d132912 p = 0) : d134175 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85871 q = 0) : d87177 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85871, d87177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85871, d87177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro222 q selected
  have h2 (q : Pattern) (selected : d85872 q = 0) : d87178 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85872, d87178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85872, d87178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85758 q = 0) : d87077 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85758, d87077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85758, d87077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
  have h4 (q : Pattern) (selected : d85759 q = 0) : d87078 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85759, d87078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85759, d87078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85873 q = 0) : d87179 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85873, d87179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85873, d87179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85760 q = 0) : d87079 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85760, d87079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85760, d87079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d132911 q = 0) : d134174 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d132911, d134174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d132911, d134174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d132912 q = 0) : d134175 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d132912, d134175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d132912, d134175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11252 (p : Pattern) (selected : d132918 p = 0) : d134181 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132913 q = 0) : d134176 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132913, d134176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11251 q selected
    | true =>
      simp only [d132913, d134176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d132914 q = 0) : d134177 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132914, d134177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132914, d134177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132806 q = 0) : d134080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132806, d134080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11231 q selected
    | true =>
      simp only [d132806, d134080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132807 q = 0) : d134081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132807, d134081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132807, d134081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d132915 q = 0) : d134178 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d132915, d134178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132915, d134178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132916 q = 0) : d134179 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d132916, d134179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d132916, d134179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d132917 q = 0) : d134180 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d132917, d134180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d132917, d134180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d132918 q = 0) : d134181 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d132918, d134181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d132918, d134181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11253 (p : Pattern) (selected : d132921 p = 0) : d134079 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85882 q = 0) : d87077 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85882, d87077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85882, d87077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro225 q selected
  have h2 (q : Pattern) (selected : d85883 q = 0) : d87078 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85883, d87078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85883, d87078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85884 q = 0) : d87079 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85884, d87079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85884, d87079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132920 q = 0) : d134078 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d132920, d134078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d132920, d134078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d132921 q = 0) : d134079 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d132921, d134079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d132921, d134079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11254 (p : Pattern) (selected : d132927 p = 0) : d134085 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132922 q = 0) : d134080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132922, d134080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11253 q selected
    | true =>
      simp only [d132922, d134080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d132923 q = 0) : d134081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132923, d134081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132923, d134081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132924 q = 0) : d134082 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d132924, d134082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132924, d134082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132925 q = 0) : d134083 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d132925, d134083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d132925, d134083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d132926 q = 0) : d134084 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d132926, d134084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d132926, d134084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d132927 q = 0) : d134085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d132927, d134085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d132927, d134085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11255 (p : Pattern) (selected : d132933 p = 0) : d134187 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132919 q = 0) : d134182 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132919, d134182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11252 q selected
    | true =>
      simp only [d132919, d134182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11232 q selected
  have h2 (q : Pattern) (selected : d132928 q = 0) : d134086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132928, d134086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11254 q selected
    | true =>
      simp only [d132928, d134086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d132929 q = 0) : d134183 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132929, d134183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d132929, d134183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d132812 q = 0) : d134086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132812, d134086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11232 q selected
    | true =>
      simp only [d132812, d134086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d132813 q = 0) : d134087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132813, d134087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d132813, d134087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d132930 q = 0) : d134184 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132930, d134184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d132930, d134184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d132931 q = 0) : d134185 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132931, d134185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132931, d134185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d132932 q = 0) : d134186 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132932, d134186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132932, d134186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d132933 q = 0) : d134187 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132933, d134187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132933, d134187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11256 (p : Pattern) (selected : d132939 p = 0) : d134193 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132834 q = 0) : d134108 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132834, d134108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132834, d134108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11235 q selected
  have h2 (q : Pattern) (selected : d132835 q = 0) : d134109 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132835, d134109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d132835, d134109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d132841 q = 0) : d134115 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132841, d134115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11235 q selected
    | true =>
      simp only [d132841, d134115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11236 q selected
  have h4 (q : Pattern) (selected : d132842 q = 0) : d134116 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132842, d134116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d132842, d134116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d132843 q = 0) : d134117 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132843, d134117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132843, d134117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132897 q = 0) : d134160 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132897, d134160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11243 q selected
    | true =>
      simp only [d132897, d134160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11248 q selected
  have h7 (q : Pattern) (selected : d132899 q = 0) : d134162 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132899, d134162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11249 q selected
    | true =>
      simp only [d132899, d134162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d132900 q = 0) : d134163 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132900, d134163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d132900, d134163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d132901 q = 0) : d134164 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132901, d134164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d132901, d134164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d132902 q = 0) : d134165 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132902, d134165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d132902, d134165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d132906 q = 0) : d134169 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132906, d134169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132906, d134169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11250 q selected
  have h12 (q : Pattern) (selected : d132907 q = 0) : d134170 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132907, d134170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d132907, d134170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d132908 q = 0) : d134171 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132908, d134171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d132908, d134171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d132909 q = 0) : d134172 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132909, d134172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d132909, d134172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d132910 q = 0) : d134173 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132910, d134173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d132910, d134173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d132934 q = 0) : d134188 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132934, d134188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132934, d134188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11255 q selected
  have h17 (q : Pattern) (selected : d132935 q = 0) : d134189 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132935, d134189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d132935, d134189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d132936 q = 0) : d134190 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132936, d134190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d132936, d134190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d132937 q = 0) : d134191 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132937, d134191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d132937, d134191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d132938 q = 0) : d134192 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132938, d134192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d132938, d134192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d132939 q = 0) : d134193 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132939, d134193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d132939, d134193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro11257 (p : Pattern) (selected : d132945 p = 0) : d134199 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132824 q = 0) : d134098 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132824, d134098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132824, d134098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11234 q selected
  have h2 (q : Pattern) (selected : d132825 q = 0) : d134099 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132825, d134099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132825, d134099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132826 q = 0) : d134100 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132826, d134100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132826, d134100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d132827 q = 0) : d134101 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132827, d134101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132827, d134101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d132828 q = 0) : d134102 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132828, d134102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132828, d134102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132940 q = 0) : d134194 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132940, d134194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132940, d134194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11256 q selected
  have h7 (q : Pattern) (selected : d132941 q = 0) : d134195 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132941, d134195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132941, d134195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d132942 q = 0) : d134196 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132942, d134196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132942, d134196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d132943 q = 0) : d134197 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132943, d134197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132943, d134197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d132944 q = 0) : d134198 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132944, d134198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132944, d134198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d132945 q = 0) : d134199 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132945, d134199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d132945, d134199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11258 (p : Pattern) (selected : d132950 p = 0) : d134204 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132864 q = 0) : d134138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132864, d134138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11240 q selected
    | true =>
      simp only [d132864, d134138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11226 q selected
  have h2 (q : Pattern) (selected : d132946 q = 0) : d134200 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132946, d134200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132946, d134200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132947 q = 0) : d134201 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132947, d134201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132947, d134201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132948 q = 0) : d134202 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132948, d134202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132948, d134202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d132949 q = 0) : d134203 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132949, d134203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132949, d134203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132950 q = 0) : d134204 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132950, d134204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132950, d134204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11259 (p : Pattern) (selected : d132957 p = 0) : d134211 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132864 q = 0) : d134138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132864, d134138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11240 q selected
    | true =>
      simp only [d132864, d134138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11226 q selected
  have h2 (q : Pattern) (selected : d132946 q = 0) : d134200 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132946, d134200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132946, d134200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132947 q = 0) : d134201 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132947, d134201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132947, d134201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132948 q = 0) : d134202 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132948, d134202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132948, d134202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d132949 q = 0) : d134203 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132949, d134203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132949, d134203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132889 q = 0) : d134154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132889, d134154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11246 q selected
    | true =>
      simp only [d132889, d134154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11228 q selected
  have h7 (q : Pattern) (selected : d132953 q = 0) : d134207 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132953, d134207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132953, d134207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d132954 q = 0) : d134208 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132954, d134208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d132954, d134208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d132955 q = 0) : d134209 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132955, d134209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132955, d134209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d132956 q = 0) : d134210 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132956, d134210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132956, d134210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d132957 q = 0) : d134211 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132957, d134211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d132957, d134211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11260 (p : Pattern) (selected : d132962 p = 0) : d134216 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132858 q = 0) : d134132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132858, d134132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11239 q selected
    | true =>
      simp only [d132858, d134132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d132859 q = 0) : d134133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132859, d134133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132859, d134133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132775 q = 0) : d134049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132775, d134049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11225 q selected
    | true =>
      simp only [d132775, d134049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132776 q = 0) : d134050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132776, d134050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132776, d134050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d132860 q = 0) : d134134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d132860, d134134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132860, d134134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132861 q = 0) : d134135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d132861, d134135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d132861, d134135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d132961 q = 0) : d134215 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d132961, d134215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132961, d134215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d132962 q = 0) : d134216 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d132962, d134216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132962, d134216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11261 (p : Pattern) (selected : d132969 p = 0) : d134223 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132858 q = 0) : d134132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132858, d134132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11239 q selected
    | true =>
      simp only [d132858, d134132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d132859 q = 0) : d134133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132859, d134133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132859, d134133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132775 q = 0) : d134049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132775, d134049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11225 q selected
    | true =>
      simp only [d132775, d134049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132776 q = 0) : d134050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132776, d134050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132776, d134050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d132860 q = 0) : d134134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d132860, d134134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132860, d134134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132967 q = 0) : d134221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d132967, d134221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132967, d134221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d132968 q = 0) : d134222 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d132968, d134222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d132968, d134222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d132969 q = 0) : d134223 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d132969, d134223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132969, d134223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11262 (p : Pattern) (selected : d132974 p = 0) : d134228 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85937 q = 0) : d87232 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85937, d87232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85937, d87232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro236 q selected
  have h2 (q : Pattern) (selected : d85938 q = 0) : d87233 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85938, d87233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85938, d87233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85812 q = 0) : d87131 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85812, d87131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85812, d87131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro206 q selected
  have h4 (q : Pattern) (selected : d85813 q = 0) : d87132 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85813, d87132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85813, d87132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85939 q = 0) : d87234 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85939, d87234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85939, d87234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85725 q = 0) : d87044 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85725, d87044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85725, d87044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
  have h7 (q : Pattern) (selected : d85726 q = 0) : d87045 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85726, d87045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85726, d87045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d85814 q = 0) : d87133 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85814, d87133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85814, d87133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d132973 q = 0) : d134227 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d132973, d134227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d132973, d134227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d132974 q = 0) : d134228 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d132974, d134228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d132974, d134228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11263 (p : Pattern) (selected : d132980 p = 0) : d134234 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132975 q = 0) : d134229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132975, d134229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11262 q selected
    | true =>
      simp only [d132975, d134229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d132976 q = 0) : d134230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132976, d134230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132976, d134230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132858 q = 0) : d134132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132858, d134132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11239 q selected
    | true =>
      simp only [d132858, d134132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132859 q = 0) : d134133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132859, d134133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132859, d134133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d132977 q = 0) : d134231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d132977, d134231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132977, d134231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132978 q = 0) : d134232 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d132978, d134232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d132978, d134232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d132979 q = 0) : d134233 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d132979, d134233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d132979, d134233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d132980 q = 0) : d134234 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d132980, d134234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132980, d134234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11264 (p : Pattern) (selected : d132983 p = 0) : d134131 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d85948 q = 0) : d87131 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85948, d87131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85948, d87131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro241 q selected
  have h2 (q : Pattern) (selected : d85949 q = 0) : d87132 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85949, d87132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85949, d87132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85823 q = 0) : d87044 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85823, d87044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85823, d87044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro211 q selected
  have h4 (q : Pattern) (selected : d85824 q = 0) : d87045 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85824, d87045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85824, d87045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d85950 q = 0) : d87133 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85950, d87133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85950, d87133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85825 q = 0) : d87046 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85825, d87046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85825, d87046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d132982 q = 0) : d134130 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d132982, d134130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d132982, d134130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d132983 q = 0) : d134131 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d132983, d134131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d132983, d134131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11265 (p : Pattern) (selected : d132989 p = 0) : d134137 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132984 q = 0) : d134132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132984, d134132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11264 q selected
    | true =>
      simp only [d132984, d134132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d132985 q = 0) : d134133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132985, d134133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132985, d134133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132867 q = 0) : d134049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132867, d134049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11241 q selected
    | true =>
      simp only [d132867, d134049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132868 q = 0) : d134050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132868, d134050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132868, d134050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d132986 q = 0) : d134134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d132986, d134134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132986, d134134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132987 q = 0) : d134135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d132987, d134135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d132987, d134135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d132988 q = 0) : d134136 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d132988, d134136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d132988, d134136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d132989 q = 0) : d134137 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d132989, d134137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132989, d134137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11266 (p : Pattern) (selected : d132995 p = 0) : d134240 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132858 q = 0) : d134132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132858, d134132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11239 q selected
    | true =>
      simp only [d132858, d134132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d132859 q = 0) : d134133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132859, d134133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132859, d134133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132992 q = 0) : d134237 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d132992, d134237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132992, d134237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132993 q = 0) : d134238 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d132993, d134238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d132993, d134238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d132994 q = 0) : d134239 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d132994, d134239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d132994, d134239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d132995 q = 0) : d134240 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d132995, d134240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132995, d134240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11267 (p : Pattern) (selected : d133001 p = 0) : d134246 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132963 q = 0) : d134217 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132963, d134217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11260 q selected
    | true =>
      simp only [d132963, d134217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11237 q selected
  have h2 (q : Pattern) (selected : d132964 q = 0) : d134218 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132964, d134218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132964, d134218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132965 q = 0) : d134219 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132965, d134219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132965, d134219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132966 q = 0) : d134220 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132966, d134220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132966, d134220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d132970 q = 0) : d134224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132970, d134224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11261 q selected
    | true =>
      simp only [d132970, d134224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11238 q selected
  have h6 (q : Pattern) (selected : d132971 q = 0) : d134225 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132971, d134225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132971, d134225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d132972 q = 0) : d134226 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132972, d134226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d132972, d134226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d132981 q = 0) : d134235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132981, d134235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11263 q selected
    | true =>
      simp only [d132981, d134235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11240 q selected
  have h9 (q : Pattern) (selected : d132990 q = 0) : d134138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132990, d134138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11265 q selected
    | true =>
      simp only [d132990, d134138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11242 q selected
  have h10 (q : Pattern) (selected : d132991 q = 0) : d134236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132991, d134236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d132991, d134236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d132996 q = 0) : d134241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132996, d134241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11266 q selected
    | true =>
      simp only [d132996, d134241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d132997 q = 0) : d134242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132997, d134242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d132997, d134242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d132998 q = 0) : d134243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132998, d134243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d132998, d134243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d132999 q = 0) : d134244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132999, d134244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d132999, d134244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d133000 q = 0) : d134245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133000, d134245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133000, d134245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d133001 q = 0) : d134246 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133001, d134246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133001, d134246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro11268 (p : Pattern) (selected : d133002 p = 0) : d134247 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132858 q = 0) : d134132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132858, d134132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11239 q selected
    | true =>
      simp only [d132858, d134132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d132859 q = 0) : d134133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132859, d134133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132859, d134133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132775 q = 0) : d134049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132775, d134049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11225 q selected
    | true =>
      simp only [d132775, d134049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132776 q = 0) : d134050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132776, d134050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132776, d134050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d132860 q = 0) : d134134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d132860, d134134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132860, d134134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132861 q = 0) : d134135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d132861, d134135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d132861, d134135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d132961 q = 0) : d134215 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d132961, d134215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132961, d134215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133002 q = 0) : d134247 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133002, d134247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133002, d134247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11269 (p : Pattern) (selected : d133007 p = 0) : d134252 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132858 q = 0) : d134132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132858, d134132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11239 q selected
    | true =>
      simp only [d132858, d134132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d132859 q = 0) : d134133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132859, d134133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132859, d134133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132775 q = 0) : d134049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132775, d134049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11225 q selected
    | true =>
      simp only [d132775, d134049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132776 q = 0) : d134050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132776, d134050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132776, d134050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d132860 q = 0) : d134134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d132860, d134134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132860, d134134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132967 q = 0) : d134221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d132967, d134221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132967, d134221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d132968 q = 0) : d134222 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d132968, d134222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d132968, d134222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133007 q = 0) : d134252 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133007, d134252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133007, d134252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11270 (p : Pattern) (selected : d133011 p = 0) : d134256 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132975 q = 0) : d134229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132975, d134229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11262 q selected
    | true =>
      simp only [d132975, d134229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d132976 q = 0) : d134230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132976, d134230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132976, d134230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132858 q = 0) : d134132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132858, d134132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11239 q selected
    | true =>
      simp only [d132858, d134132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132859 q = 0) : d134133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132859, d134133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132859, d134133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d132977 q = 0) : d134231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d132977, d134231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132977, d134231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132978 q = 0) : d134232 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d132978, d134232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d132978, d134232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d132979 q = 0) : d134233 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d132979, d134233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d132979, d134233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133011 q = 0) : d134256 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133011, d134256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133011, d134256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11271 (p : Pattern) (selected : d133013 p = 0) : d134153 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132984 q = 0) : d134132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132984, d134132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11264 q selected
    | true =>
      simp only [d132984, d134132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d132985 q = 0) : d134133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132985, d134133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132985, d134133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132867 q = 0) : d134049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132867, d134049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11241 q selected
    | true =>
      simp only [d132867, d134049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132868 q = 0) : d134050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132868, d134050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132868, d134050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d132986 q = 0) : d134134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d132986, d134134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132986, d134134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132987 q = 0) : d134135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d132987, d134135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d132987, d134135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d132988 q = 0) : d134136 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d132988, d134136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d132988, d134136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133013 q = 0) : d134153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133013, d134153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133013, d134153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11272 (p : Pattern) (selected : d133016 p = 0) : d134259 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132858 q = 0) : d134132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132858, d134132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11239 q selected
    | true =>
      simp only [d132858, d134132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d132859 q = 0) : d134133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132859, d134133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132859, d134133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132992 q = 0) : d134237 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d132992, d134237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132992, d134237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132993 q = 0) : d134238 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d132993, d134238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d132993, d134238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d132994 q = 0) : d134239 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d132994, d134239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d132994, d134239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133016 q = 0) : d134259 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133016, d134259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133016, d134259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11273 (p : Pattern) (selected : d133022 p = 0) : d134265 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132963 q = 0) : d134217 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132963, d134217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11260 q selected
    | true =>
      simp only [d132963, d134217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11237 q selected
  have h2 (q : Pattern) (selected : d132964 q = 0) : d134218 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132964, d134218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132964, d134218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132965 q = 0) : d134219 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132965, d134219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132965, d134219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132966 q = 0) : d134220 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132966, d134220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132966, d134220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d132970 q = 0) : d134224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132970, d134224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11261 q selected
    | true =>
      simp only [d132970, d134224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11238 q selected
  have h6 (q : Pattern) (selected : d132971 q = 0) : d134225 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132971, d134225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132971, d134225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d132972 q = 0) : d134226 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132972, d134226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d132972, d134226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d132981 q = 0) : d134235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132981, d134235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11263 q selected
    | true =>
      simp only [d132981, d134235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11240 q selected
  have h9 (q : Pattern) (selected : d132990 q = 0) : d134138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132990, d134138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11265 q selected
    | true =>
      simp only [d132990, d134138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11242 q selected
  have h10 (q : Pattern) (selected : d132991 q = 0) : d134236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132991, d134236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d132991, d134236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d132996 q = 0) : d134241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132996, d134241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11266 q selected
    | true =>
      simp only [d132996, d134241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d132997 q = 0) : d134242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132997, d134242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d132997, d134242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d132998 q = 0) : d134243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132998, d134243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d132998, d134243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d132999 q = 0) : d134244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132999, d134244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d132999, d134244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d133000 q = 0) : d134245 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133000, d134245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133000, d134245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d133003 q = 0) : d134248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133003, d134248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11268 q selected
    | true =>
      simp only [d133003, d134248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11244 q selected
  have h17 (q : Pattern) (selected : d133004 q = 0) : d134249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133004, d134249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133004, d134249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d133005 q = 0) : d134250 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133005, d134250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d133005, d134250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d133006 q = 0) : d134251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133006, d134251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133006, d134251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d133008 q = 0) : d134253 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133008, d134253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11269 q selected
    | true =>
      simp only [d133008, d134253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11245 q selected
  have h21 (q : Pattern) (selected : d133009 q = 0) : d134254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133009, d134254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133009, d134254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d133010 q = 0) : d134255 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133010, d134255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d133010, d134255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d133012 q = 0) : d134257 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133012, d134257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11270 q selected
    | true =>
      simp only [d133012, d134257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11246 q selected
  have h24 (q : Pattern) (selected : d133014 q = 0) : d134154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133014, d134154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11271 q selected
    | true =>
      simp only [d133014, d134154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11247 q selected
  have h25 (q : Pattern) (selected : d133015 q = 0) : d134258 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133015, d134258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d133015, d134258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d133017 q = 0) : d134260 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133017, d134260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11272 q selected
    | true =>
      simp only [d133017, d134260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d133018 q = 0) : d134261 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133018, d134261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d133018, d134261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d133019 q = 0) : d134262 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133019, d134262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d133019, d134262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d133020 q = 0) : d134263 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133020, d134263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d133020, d134263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d133021 q = 0) : d134264 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133021, d134264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d133021, d134264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d133022 q = 0) : d134265 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133022, d134265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d133022, d134265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro11274 (p : Pattern) (selected : d133024 p = 0) : d134267 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132864 q = 0) : d134138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132864, d134138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11240 q selected
    | true =>
      simp only [d132864, d134138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11226 q selected
  have h2 (q : Pattern) (selected : d132946 q = 0) : d134200 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132946, d134200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132946, d134200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132947 q = 0) : d134201 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132947, d134201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132947, d134201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132948 q = 0) : d134202 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132948, d134202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132948, d134202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d132949 q = 0) : d134203 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132949, d134203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132949, d134203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132781 q = 0) : d134055 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132781, d134055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11226 q selected
    | true =>
      simp only [d132781, d134055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d132829 q = 0) : d134103 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132829, d134103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132829, d134103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d132830 q = 0) : d134104 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132830, d134104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d132830, d134104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d132831 q = 0) : d134105 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132831, d134105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132831, d134105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d132832 q = 0) : d134106 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132832, d134106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132832, d134106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133024 q = 0) : d134267 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133024, d134267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133024, d134267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11275 (p : Pattern) (selected : d133031 p = 0) : d134274 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133012 q = 0) : d134257 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133012, d134257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11270 q selected
    | true =>
      simp only [d133012, d134257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11246 q selected
  have h2 (q : Pattern) (selected : d133014 q = 0) : d134154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133014, d134154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11271 q selected
    | true =>
      simp only [d133014, d134154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11247 q selected
  have h3 (q : Pattern) (selected : d133015 q = 0) : d134258 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133015, d134258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133015, d134258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133017 q = 0) : d134260 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133017, d134260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11272 q selected
    | true =>
      simp only [d133017, d134260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133018 q = 0) : d134261 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133018, d134261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133018, d134261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133019 q = 0) : d134262 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133019, d134262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133019, d134262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133029 q = 0) : d134272 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133029, d134272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133029, d134272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133030 q = 0) : d134273 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133030, d134273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133030, d134273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133031 q = 0) : d134274 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133031, d134274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133031, d134274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11276 (p : Pattern) (selected : d133033 p = 0) : d134276 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132788 q = 0) : d134062 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132788, d134062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11228 q selected
    | true =>
      simp only [d132788, d134062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d132836 q = 0) : d134110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132836, d134110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132836, d134110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132837 q = 0) : d134111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132837, d134111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132837, d134111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132838 q = 0) : d134112 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132838, d134112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132838, d134112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d132839 q = 0) : d134113 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132839, d134113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132839, d134113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133033 q = 0) : d134276 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133033, d134276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133033, d134276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11277 (p : Pattern) (selected : d133040 p = 0) : d134283 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86007 q = 0) : d87289 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86007, d87289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86007, d87289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro253 q selected
  have h2 (q : Pattern) (selected : d86008 q = 0) : d87290 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86008, d87290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86008, d87290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85871 q = 0) : d87177 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85871, d87177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85871, d87177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro222 q selected
  have h4 (q : Pattern) (selected : d85872 q = 0) : d87178 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85872, d87178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85872, d87178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86009 q = 0) : d87291 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86009, d87291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86009, d87291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85758 q = 0) : d87077 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85758, d87077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85758, d87077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
  have h7 (q : Pattern) (selected : d85759 q = 0) : d87078 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85759, d87078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85759, d87078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d85873 q = 0) : d87179 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85873, d87179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85873, d87179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133039 q = 0) : d134282 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133039, d134282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133039, d134282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133040 q = 0) : d134283 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133040, d134283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133040, d134283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11278 (p : Pattern) (selected : d133046 p = 0) : d134289 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133041 q = 0) : d134284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133041, d134284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11277 q selected
    | true =>
      simp only [d133041, d134284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133042 q = 0) : d134285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133042, d134285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133042, d134285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132913 q = 0) : d134176 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132913, d134176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11251 q selected
    | true =>
      simp only [d132913, d134176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132914 q = 0) : d134177 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132914, d134177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132914, d134177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133043 q = 0) : d134286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133043, d134286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133043, d134286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133044 q = 0) : d134287 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133044, d134287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133044, d134287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133045 q = 0) : d134288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133045, d134288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133045, d134288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133046 q = 0) : d134289 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133046, d134289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133046, d134289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11279 (p : Pattern) (selected : d133049 p = 0) : d134175 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86018 q = 0) : d87177 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86018, d87177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86018, d87177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro256 q selected
  have h2 (q : Pattern) (selected : d86019 q = 0) : d87178 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86019, d87178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86019, d87178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85882 q = 0) : d87077 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85882, d87077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85882, d87077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro225 q selected
  have h4 (q : Pattern) (selected : d85883 q = 0) : d87078 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85883, d87078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85883, d87078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86020 q = 0) : d87179 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86020, d87179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86020, d87179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d85884 q = 0) : d87079 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85884, d87079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85884, d87079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133048 q = 0) : d134174 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133048, d134174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133048, d134174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133049 q = 0) : d134175 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133049, d134175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133049, d134175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11280 (p : Pattern) (selected : d133055 p = 0) : d134181 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133050 q = 0) : d134176 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133050, d134176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11279 q selected
    | true =>
      simp only [d133050, d134176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133051 q = 0) : d134177 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133051, d134177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133051, d134177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132922 q = 0) : d134080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132922, d134080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11253 q selected
    | true =>
      simp only [d132922, d134080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132923 q = 0) : d134081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132923, d134081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132923, d134081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133052 q = 0) : d134178 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133052, d134178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133052, d134178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133053 q = 0) : d134179 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133053, d134179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133053, d134179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133054 q = 0) : d134180 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133054, d134180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133054, d134180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133055 q = 0) : d134181 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133055, d134181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133055, d134181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11281 (p : Pattern) (selected : d133061 p = 0) : d134295 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132913 q = 0) : d134176 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132913, d134176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11251 q selected
    | true =>
      simp only [d132913, d134176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d132914 q = 0) : d134177 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132914, d134177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132914, d134177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133058 q = 0) : d134292 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133058, d134292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133058, d134292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133059 q = 0) : d134293 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133059, d134293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133059, d134293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133060 q = 0) : d134294 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133060, d134294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133060, d134294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133061 q = 0) : d134295 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133061, d134295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133061, d134295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11282 (p : Pattern) (selected : d133067 p = 0) : d134301 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133047 q = 0) : d134290 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133047, d134290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11278 q selected
    | true =>
      simp only [d133047, d134290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11252 q selected
  have h2 (q : Pattern) (selected : d133056 q = 0) : d134182 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133056, d134182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11280 q selected
    | true =>
      simp only [d133056, d134182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11254 q selected
  have h3 (q : Pattern) (selected : d133057 q = 0) : d134291 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133057, d134291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133057, d134291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133062 q = 0) : d134296 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133062, d134296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11281 q selected
    | true =>
      simp only [d133062, d134296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133063 q = 0) : d134297 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133063, d134297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133063, d134297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133064 q = 0) : d134298 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133064, d134298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133064, d134298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133065 q = 0) : d134299 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133065, d134299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133065, d134299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133066 q = 0) : d134300 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133066, d134300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133066, d134300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133067 q = 0) : d134301 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133067, d134301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133067, d134301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11283 (p : Pattern) (selected : d133073 p = 0) : d134307 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132812 q = 0) : d134086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132812, d134086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11232 q selected
    | true =>
      simp only [d132812, d134086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133069 q = 0) : d134303 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133069, d134303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133069, d134303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133070 q = 0) : d134304 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133070, d134304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133070, d134304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133071 q = 0) : d134305 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133071, d134305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133071, d134305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133072 q = 0) : d134306 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133072, d134306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133072, d134306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133073 q = 0) : d134307 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133073, d134307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133073, d134307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11284 (p : Pattern) (selected : d133079 p = 0) : d134313 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d132951 q = 0) : d134205 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132951, d134205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132951, d134205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11258 q selected
  have h2 (q : Pattern) (selected : d132952 q = 0) : d134206 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132952, d134206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d132952, d134206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d132958 q = 0) : d134212 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132958, d134212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11258 q selected
    | true =>
      simp only [d132958, d134212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11259 q selected
  have h4 (q : Pattern) (selected : d132959 q = 0) : d134213 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132959, d134213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d132959, d134213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d132960 q = 0) : d134214 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132960, d134214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132960, d134214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133023 q = 0) : d134266 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133023, d134266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11267 q selected
    | true =>
      simp only [d133023, d134266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11273 q selected
  have h7 (q : Pattern) (selected : d133025 q = 0) : d134268 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133025, d134268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11274 q selected
    | true =>
      simp only [d133025, d134268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11236 q selected
  have h8 (q : Pattern) (selected : d133026 q = 0) : d134269 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133026, d134269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133026, d134269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133027 q = 0) : d134270 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133027, d134270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d133027, d134270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d133028 q = 0) : d134271 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133028, d134271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133028, d134271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133032 q = 0) : d134275 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133032, d134275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133032, d134275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11275 q selected
  have h12 (q : Pattern) (selected : d133034 q = 0) : d134277 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133034, d134277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133034, d134277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11276 q selected
  have h13 (q : Pattern) (selected : d133035 q = 0) : d134278 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133035, d134278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d133035, d134278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d133036 q = 0) : d134279 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133036, d134279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d133036, d134279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d133037 q = 0) : d134280 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133037, d134280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d133037, d134280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d133038 q = 0) : d134281 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d133038, d134281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133038, d134281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d133068 q = 0) : d134302 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133068, d134302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133068, d134302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11282 q selected
  have h18 (q : Pattern) (selected : d133074 q = 0) : d134308 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133074, d134308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133074, d134308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11283 q selected
  have h19 (q : Pattern) (selected : d133075 q = 0) : d134309 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133075, d134309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d133075, d134309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d133076 q = 0) : d134310 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133076, d134310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d133076, d134310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d133077 q = 0) : d134311 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133077, d134311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d133077, d134311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d133078 q = 0) : d134312 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d133078, d134312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d133078, d134312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d133079 q = 0) : d134313 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d133079, d134313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d133079, d134313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro11285 (p : Pattern) (selected : d133085 p = 0) : d134319 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133080 q = 0) : d134314 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d133080, d134314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133080, d134314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11284 q selected
  have h2 (q : Pattern) (selected : d133081 q = 0) : d134315 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d133081, d134315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133081, d134315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133082 q = 0) : d134316 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d133082, d134316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133082, d134316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133083 q = 0) : d134317 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d133083, d134317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133083, d134317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133084 q = 0) : d134318 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d133084, d134318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133084, d134318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133085 q = 0) : d134319 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d133085, d134319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133085, d134319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11286 (p : Pattern) (selected : d133088 p = 0) : d134322 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86059 q = 0) : d87330 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86059, d87330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86059, d87330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro319 q selected
  have h2 (q : Pattern) (selected : d86060 q = 0) : d87331 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86060, d87331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86060, d87331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86061 q = 0) : d87332 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86061, d87332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86061, d87332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro320 q selected
  have h4 (q : Pattern) (selected : d86062 q = 0) : d87333 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86062, d87333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86062, d87333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86063 q = 0) : d87334 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86063, d87334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86063, d87334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86067 q = 0) : d87338 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86067, d87338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86067, d87338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133087 q = 0) : d134321 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133087, d134321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133087, d134321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133088 q = 0) : d134322 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133088, d134322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133088, d134322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11287 (p : Pattern) (selected : d133092 p = 0) : d134326 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86061 q = 0) : d87332 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86061, d87332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86061, d87332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro320 q selected
  have h2 (q : Pattern) (selected : d86062 q = 0) : d87333 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86062, d87333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86062, d87333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86067 q = 0) : d87338 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86067, d87338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86067, d87338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133091 q = 0) : d134325 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133091, d134325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133091, d134325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133092 q = 0) : d134326 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133092, d134326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133092, d134326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11288 (p : Pattern) (selected : d133098 p = 0) : d134332 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133089 q = 0) : d134323 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133089, d134323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11286 q selected
    | true =>
      simp only [d133089, d134323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133090 q = 0) : d134324 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133090, d134324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133090, d134324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133093 q = 0) : d134327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11287 q selected
    | true =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133094 q = 0) : d134328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133095 q = 0) : d134329 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133095, d134329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133095, d134329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133096 q = 0) : d134330 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133096, d134330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133096, d134330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133097 q = 0) : d134331 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133097, d134331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133097, d134331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133098 q = 0) : d134332 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133098, d134332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133098, d134332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11289 (p : Pattern) (selected : d133102 p = 0) : d134336 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133093 q = 0) : d134327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11287 q selected
    | true =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133094 q = 0) : d134328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133099 q = 0) : d134333 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133099, d134333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133099, d134333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133100 q = 0) : d134334 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133100, d134334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133100, d134334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133101 q = 0) : d134335 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133101, d134335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133101, d134335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133102 q = 0) : d134336 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133102, d134336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133102, d134336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11290 (p : Pattern) (selected : d133108 p = 0) : d134342 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133103 q = 0) : d134337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133103, d134337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11288 q selected
    | true =>
      simp only [d133103, d134337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11289 q selected
  have h2 (q : Pattern) (selected : d133104 q = 0) : d134338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133104, d134338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133104, d134338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133105 q = 0) : d134339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133105, d134339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133105, d134339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133106 q = 0) : d134340 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133106, d134340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133106, d134340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133107 q = 0) : d134341 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133107, d134341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133107, d134341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133108 q = 0) : d134342 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133108, d134342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133108, d134342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11291 (p : Pattern) (selected : d133111 p = 0) : d134345 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133089 q = 0) : d134323 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133089, d134323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11286 q selected
    | true =>
      simp only [d133089, d134323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133090 q = 0) : d134324 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133090, d134324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133090, d134324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133093 q = 0) : d134327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11287 q selected
    | true =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133094 q = 0) : d134328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133095 q = 0) : d134329 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133095, d134329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133095, d134329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133096 q = 0) : d134330 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133096, d134330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133096, d134330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133097 q = 0) : d134331 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133097, d134331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133097, d134331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133111 q = 0) : d134345 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133111, d134345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133111, d134345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11292 (p : Pattern) (selected : d133112 p = 0) : d134346 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133093 q = 0) : d134327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11287 q selected
    | true =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133094 q = 0) : d134328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133099 q = 0) : d134333 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133099, d134333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133099, d134333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133100 q = 0) : d134334 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133100, d134334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133100, d134334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133101 q = 0) : d134335 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133101, d134335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133101, d134335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133112 q = 0) : d134346 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133112, d134346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133112, d134346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11293 (p : Pattern) (selected : d133118 p = 0) : d134352 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133103 q = 0) : d134337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133103, d134337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11288 q selected
    | true =>
      simp only [d133103, d134337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11289 q selected
  have h2 (q : Pattern) (selected : d133104 q = 0) : d134338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133104, d134338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133104, d134338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133105 q = 0) : d134339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133105, d134339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133105, d134339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133106 q = 0) : d134340 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133106, d134340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133106, d134340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133107 q = 0) : d134341 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133107, d134341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133107, d134341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133113 q = 0) : d134347 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133113, d134347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11291 q selected
    | true =>
      simp only [d133113, d134347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11292 q selected
  have h7 (q : Pattern) (selected : d133114 q = 0) : d134348 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133114, d134348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133114, d134348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133115 q = 0) : d134349 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133115, d134349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133115, d134349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d133116 q = 0) : d134350 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133116, d134350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133116, d134350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133117 q = 0) : d134351 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133117, d134351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133117, d134351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133118 q = 0) : d134352 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133118, d134352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133118, d134352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11294 (p : Pattern) (selected : d133123 p = 0) : d134357 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133089 q = 0) : d134323 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133089, d134323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11286 q selected
    | true =>
      simp only [d133089, d134323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133090 q = 0) : d134324 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133090, d134324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133090, d134324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133093 q = 0) : d134327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11287 q selected
    | true =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133094 q = 0) : d134328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133095 q = 0) : d134329 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133095, d134329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133095, d134329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133096 q = 0) : d134330 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133096, d134330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133096, d134330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133122 q = 0) : d134356 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133122, d134356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133122, d134356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133123 q = 0) : d134357 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133123, d134357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133123, d134357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11295 (p : Pattern) (selected : d133125 p = 0) : d134359 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133093 q = 0) : d134327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11287 q selected
    | true =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133094 q = 0) : d134328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133099 q = 0) : d134333 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133099, d134333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133099, d134333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133100 q = 0) : d134334 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133100, d134334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133100, d134334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133124 q = 0) : d134358 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133124, d134358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133124, d134358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133125 q = 0) : d134359 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133125, d134359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133125, d134359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11296 (p : Pattern) (selected : d133132 p = 0) : d134366 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133089 q = 0) : d134323 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133089, d134323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11286 q selected
    | true =>
      simp only [d133089, d134323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133090 q = 0) : d134324 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133090, d134324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133090, d134324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133093 q = 0) : d134327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11287 q selected
    | true =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133094 q = 0) : d134328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133095 q = 0) : d134329 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133095, d134329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133095, d134329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133130 q = 0) : d134364 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133130, d134364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133130, d134364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133131 q = 0) : d134365 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133131, d134365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133131, d134365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133132 q = 0) : d134366 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133132, d134366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133132, d134366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11297 (p : Pattern) (selected : d133135 p = 0) : d134369 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133093 q = 0) : d134327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11287 q selected
    | true =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133094 q = 0) : d134328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133099 q = 0) : d134333 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133099, d134333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133099, d134333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133133 q = 0) : d134367 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133133, d134367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133133, d134367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133134 q = 0) : d134368 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133134, d134368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133134, d134368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133135 q = 0) : d134369 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133135, d134369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133135, d134369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11298 (p : Pattern) (selected : d133140 p = 0) : d134374 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86115 q = 0) : d87386 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86115, d87386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86115, d87386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro318 q selected
  have h2 (q : Pattern) (selected : d86116 q = 0) : d87387 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86116, d87387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86116, d87387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86059 q = 0) : d87330 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86059, d87330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86059, d87330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro319 q selected
  have h4 (q : Pattern) (selected : d86060 q = 0) : d87331 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86060, d87331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86060, d87331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86117 q = 0) : d87388 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86117, d87388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86117, d87388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86061 q = 0) : d87332 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86061, d87332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86061, d87332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro320 q selected
  have h7 (q : Pattern) (selected : d86062 q = 0) : d87333 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86062, d87333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86062, d87333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86063 q = 0) : d87334 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86063, d87334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86063, d87334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133139 q = 0) : d134373 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133139, d134373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133139, d134373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133140 q = 0) : d134374 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133140, d134374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133140, d134374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11299 (p : Pattern) (selected : d133146 p = 0) : d134380 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133141 q = 0) : d134375 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133141, d134375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11298 q selected
    | true =>
      simp only [d133141, d134375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133142 q = 0) : d134376 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133142, d134376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133142, d134376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133089 q = 0) : d134323 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133089, d134323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11286 q selected
    | true =>
      simp only [d133089, d134323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133090 q = 0) : d134324 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133090, d134324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133090, d134324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133143 q = 0) : d134377 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133143, d134377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133143, d134377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133144 q = 0) : d134378 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133144, d134378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133144, d134378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133145 q = 0) : d134379 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133145, d134379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133145, d134379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133146 q = 0) : d134380 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133146, d134380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133146, d134380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11300 (p : Pattern) (selected : d133149 p = 0) : d134322 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86126 q = 0) : d87330 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86126, d87330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86126, d87330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro344 q selected
  have h2 (q : Pattern) (selected : d86127 q = 0) : d87331 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86127, d87331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86127, d87331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86128 q = 0) : d87332 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86128, d87332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86128, d87332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro345 q selected
  have h4 (q : Pattern) (selected : d86129 q = 0) : d87333 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86129, d87333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86129, d87333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86130 q = 0) : d87334 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86130, d87334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86130, d87334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86134 q = 0) : d87338 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86134, d87338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86134, d87338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133148 q = 0) : d134321 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133148, d134321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133148, d134321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133149 q = 0) : d134322 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133149, d134322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133149, d134322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11301 (p : Pattern) (selected : d133153 p = 0) : d134326 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86128 q = 0) : d87332 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86128, d87332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86128, d87332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro345 q selected
  have h2 (q : Pattern) (selected : d86129 q = 0) : d87333 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86129, d87333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86129, d87333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86134 q = 0) : d87338 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86134, d87338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86134, d87338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133152 q = 0) : d134325 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133152, d134325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133152, d134325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133153 q = 0) : d134326 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133153, d134326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133153, d134326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11302 (p : Pattern) (selected : d133159 p = 0) : d134332 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133150 q = 0) : d134323 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133150, d134323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11300 q selected
    | true =>
      simp only [d133150, d134323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133151 q = 0) : d134324 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133151, d134324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133151, d134324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133154 q = 0) : d134327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133154, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11301 q selected
    | true =>
      simp only [d133154, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133155 q = 0) : d134328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133155, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133155, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133156 q = 0) : d134329 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133156, d134329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133156, d134329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133157 q = 0) : d134330 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133157, d134330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133157, d134330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133158 q = 0) : d134331 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133158, d134331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133158, d134331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133159 q = 0) : d134332 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133159, d134332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133159, d134332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11303 (p : Pattern) (selected : d133163 p = 0) : d134336 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133154 q = 0) : d134327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133154, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11301 q selected
    | true =>
      simp only [d133154, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133155 q = 0) : d134328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133155, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133155, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133160 q = 0) : d134333 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133160, d134333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133160, d134333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133161 q = 0) : d134334 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133161, d134334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133161, d134334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133162 q = 0) : d134335 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133162, d134335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133162, d134335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133163 q = 0) : d134336 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133163, d134336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133163, d134336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11304 (p : Pattern) (selected : d133170 p = 0) : d134387 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86059 q = 0) : d87330 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86059, d87330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86059, d87330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro319 q selected
  have h2 (q : Pattern) (selected : d86060 q = 0) : d87331 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86060, d87331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86060, d87331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86061 q = 0) : d87332 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86061, d87332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86061, d87332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro320 q selected
  have h4 (q : Pattern) (selected : d86062 q = 0) : d87333 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86062, d87333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86062, d87333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86063 q = 0) : d87334 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86063, d87334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86063, d87334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133166 q = 0) : d134383 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d133166, d134383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133166, d134383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3356 q selected
  have h7 (q : Pattern) (selected : d133167 q = 0) : d134384 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d133167, d134384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133167, d134384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133168 q = 0) : d134385 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d133168, d134385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133168, d134385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d133169 q = 0) : d134386 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133169, d134386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133169, d134386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133170 q = 0) : d134387 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133170, d134387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133170, d134387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11305 (p : Pattern) (selected : d133176 p = 0) : d134393 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133171 q = 0) : d134388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133171, d134388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11304 q selected
    | true =>
      simp only [d133171, d134388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133172 q = 0) : d134389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133172, d134389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133172, d134389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133173 q = 0) : d134390 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133173, d134390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133173, d134390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133174 q = 0) : d134391 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133174, d134391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133174, d134391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133175 q = 0) : d134392 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133175, d134392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133175, d134392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133176 q = 0) : d134393 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133176, d134393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133176, d134393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11306 (p : Pattern) (selected : d133182 p = 0) : d134399 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133126 q = 0) : d134360 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133126, d134360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11294 q selected
    | true =>
      simp only [d133126, d134360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11295 q selected
  have h2 (q : Pattern) (selected : d133127 q = 0) : d134361 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133127, d134361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133127, d134361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133128 q = 0) : d134362 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133128, d134362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133128, d134362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133129 q = 0) : d134363 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133129, d134363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133129, d134363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133136 q = 0) : d134370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133136, d134370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11296 q selected
    | true =>
      simp only [d133136, d134370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11297 q selected
  have h6 (q : Pattern) (selected : d133137 q = 0) : d134371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133137, d134371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133137, d134371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133138 q = 0) : d134372 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133138, d134372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133138, d134372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133147 q = 0) : d134381 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133147, d134381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11299 q selected
    | true =>
      simp only [d133147, d134381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11288 q selected
  have h9 (q : Pattern) (selected : d133164 q = 0) : d134337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133164, d134337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11302 q selected
    | true =>
      simp only [d133164, d134337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11303 q selected
  have h10 (q : Pattern) (selected : d133165 q = 0) : d134382 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133165, d134382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d133165, d134382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133177 q = 0) : d134394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133177, d134394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11305 q selected
    | true =>
      simp only [d133177, d134394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d133178 q = 0) : d134395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133178, d134395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d133178, d134395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d133179 q = 0) : d134396 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133179, d134396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133179, d134396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d133180 q = 0) : d134397 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133180, d134397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133180, d134397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d133181 q = 0) : d134398 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133181, d134398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133181, d134398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d133182 q = 0) : d134399 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133182, d134399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133182, d134399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro11307 (p : Pattern) (selected : d133183 p = 0) : d134400 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133089 q = 0) : d134323 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133089, d134323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11286 q selected
    | true =>
      simp only [d133089, d134323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133090 q = 0) : d134324 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133090, d134324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133090, d134324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133093 q = 0) : d134327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11287 q selected
    | true =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133094 q = 0) : d134328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133095 q = 0) : d134329 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133095, d134329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133095, d134329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133096 q = 0) : d134330 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133096, d134330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133096, d134330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133122 q = 0) : d134356 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133122, d134356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133122, d134356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133183 q = 0) : d134400 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133183, d134400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133183, d134400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11308 (p : Pattern) (selected : d133184 p = 0) : d134401 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133093 q = 0) : d134327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11287 q selected
    | true =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133094 q = 0) : d134328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133099 q = 0) : d134333 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133099, d134333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133099, d134333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133100 q = 0) : d134334 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133100, d134334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133100, d134334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133124 q = 0) : d134358 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133124, d134358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133124, d134358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133184 q = 0) : d134401 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133184, d134401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133184, d134401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11309 (p : Pattern) (selected : d133189 p = 0) : d134406 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133089 q = 0) : d134323 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133089, d134323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11286 q selected
    | true =>
      simp only [d133089, d134323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133090 q = 0) : d134324 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133090, d134324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133090, d134324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133093 q = 0) : d134327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11287 q selected
    | true =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133094 q = 0) : d134328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133095 q = 0) : d134329 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133095, d134329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133095, d134329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133130 q = 0) : d134364 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133130, d134364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133130, d134364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133131 q = 0) : d134365 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133131, d134365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133131, d134365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133189 q = 0) : d134406 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133189, d134406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133189, d134406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11310 (p : Pattern) (selected : d133190 p = 0) : d134407 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133093 q = 0) : d134327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11287 q selected
    | true =>
      simp only [d133093, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133094 q = 0) : d134328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133094, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133099 q = 0) : d134333 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133099, d134333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133099, d134333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133133 q = 0) : d134367 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133133, d134367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133133, d134367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133134 q = 0) : d134368 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133134, d134368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133134, d134368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133190 q = 0) : d134407 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133190, d134407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133190, d134407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11311 (p : Pattern) (selected : d133194 p = 0) : d134411 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133141 q = 0) : d134375 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133141, d134375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11298 q selected
    | true =>
      simp only [d133141, d134375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133142 q = 0) : d134376 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133142, d134376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133142, d134376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133089 q = 0) : d134323 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133089, d134323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11286 q selected
    | true =>
      simp only [d133089, d134323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133090 q = 0) : d134324 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133090, d134324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133090, d134324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133143 q = 0) : d134377 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133143, d134377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133143, d134377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133144 q = 0) : d134378 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133144, d134378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133144, d134378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133145 q = 0) : d134379 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133145, d134379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133145, d134379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133194 q = 0) : d134411 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133194, d134411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133194, d134411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11312 (p : Pattern) (selected : d133196 p = 0) : d134345 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133150 q = 0) : d134323 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133150, d134323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11300 q selected
    | true =>
      simp only [d133150, d134323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133151 q = 0) : d134324 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133151, d134324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133151, d134324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133154 q = 0) : d134327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133154, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11301 q selected
    | true =>
      simp only [d133154, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133155 q = 0) : d134328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133155, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133155, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133156 q = 0) : d134329 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133156, d134329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133156, d134329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133157 q = 0) : d134330 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133157, d134330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133157, d134330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133158 q = 0) : d134331 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133158, d134331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133158, d134331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133196 q = 0) : d134345 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133196, d134345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133196, d134345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11313 (p : Pattern) (selected : d133197 p = 0) : d134346 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133154 q = 0) : d134327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133154, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11301 q selected
    | true =>
      simp only [d133154, d134327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133155 q = 0) : d134328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133155, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133155, d134328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133160 q = 0) : d134333 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133160, d134333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133160, d134333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133161 q = 0) : d134334 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133161, d134334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133161, d134334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133162 q = 0) : d134335 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133162, d134335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133162, d134335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133197 q = 0) : d134346 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133197, d134346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133197, d134346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11314 (p : Pattern) (selected : d133200 p = 0) : d134414 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133171 q = 0) : d134388 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133171, d134388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11304 q selected
    | true =>
      simp only [d133171, d134388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133172 q = 0) : d134389 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133172, d134389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133172, d134389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133173 q = 0) : d134390 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133173, d134390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133173, d134390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133174 q = 0) : d134391 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133174, d134391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133174, d134391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133175 q = 0) : d134392 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133175, d134392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133175, d134392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133200 q = 0) : d134414 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133200, d134414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133200, d134414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11315 (p : Pattern) (selected : d133206 p = 0) : d134420 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133126 q = 0) : d134360 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133126, d134360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11294 q selected
    | true =>
      simp only [d133126, d134360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11295 q selected
  have h2 (q : Pattern) (selected : d133127 q = 0) : d134361 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133127, d134361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133127, d134361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133128 q = 0) : d134362 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133128, d134362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133128, d134362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133129 q = 0) : d134363 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133129, d134363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133129, d134363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133136 q = 0) : d134370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133136, d134370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11296 q selected
    | true =>
      simp only [d133136, d134370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11297 q selected
  have h6 (q : Pattern) (selected : d133137 q = 0) : d134371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133137, d134371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133137, d134371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133138 q = 0) : d134372 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133138, d134372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133138, d134372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133147 q = 0) : d134381 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133147, d134381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11299 q selected
    | true =>
      simp only [d133147, d134381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11288 q selected
  have h9 (q : Pattern) (selected : d133164 q = 0) : d134337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133164, d134337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11302 q selected
    | true =>
      simp only [d133164, d134337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11303 q selected
  have h10 (q : Pattern) (selected : d133165 q = 0) : d134382 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133165, d134382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d133165, d134382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133177 q = 0) : d134394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133177, d134394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11305 q selected
    | true =>
      simp only [d133177, d134394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d133178 q = 0) : d134395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133178, d134395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d133178, d134395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d133179 q = 0) : d134396 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133179, d134396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133179, d134396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d133180 q = 0) : d134397 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133180, d134397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133180, d134397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d133181 q = 0) : d134398 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133181, d134398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133181, d134398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d133185 q = 0) : d134402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133185, d134402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11307 q selected
    | true =>
      simp only [d133185, d134402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11308 q selected
  have h17 (q : Pattern) (selected : d133186 q = 0) : d134403 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133186, d134403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133186, d134403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d133187 q = 0) : d134404 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133187, d134404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d133187, d134404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d133188 q = 0) : d134405 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133188, d134405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133188, d134405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d133191 q = 0) : d134408 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133191, d134408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11309 q selected
    | true =>
      simp only [d133191, d134408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11310 q selected
  have h21 (q : Pattern) (selected : d133192 q = 0) : d134409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133192, d134409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133192, d134409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d133193 q = 0) : d134410 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133193, d134410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d133193, d134410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d133195 q = 0) : d134412 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133195, d134412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11311 q selected
    | true =>
      simp only [d133195, d134412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11291 q selected
  have h24 (q : Pattern) (selected : d133198 q = 0) : d134347 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133198, d134347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11312 q selected
    | true =>
      simp only [d133198, d134347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11313 q selected
  have h25 (q : Pattern) (selected : d133199 q = 0) : d134413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133199, d134413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d133199, d134413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d133201 q = 0) : d134415 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133201, d134415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11314 q selected
    | true =>
      simp only [d133201, d134415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d133202 q = 0) : d134416 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133202, d134416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d133202, d134416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d133203 q = 0) : d134417 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133203, d134417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d133203, d134417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d133204 q = 0) : d134418 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133204, d134418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d133204, d134418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d133205 q = 0) : d134419 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133205, d134419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d133205, d134419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d133206 q = 0) : d134420 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133206, d134420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d133206, d134420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro11316 (p : Pattern) (selected : d133213 p = 0) : d134427 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133103 q = 0) : d134337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133103, d134337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11288 q selected
    | true =>
      simp only [d133103, d134337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11289 q selected
  have h2 (q : Pattern) (selected : d133104 q = 0) : d134338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133104, d134338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133104, d134338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133105 q = 0) : d134339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133105, d134339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133105, d134339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133106 q = 0) : d134340 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133106, d134340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133106, d134340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133107 q = 0) : d134341 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133107, d134341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133107, d134341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133208 q = 0) : d134422 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133208, d134422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11289 q selected
    | true =>
      simp only [d133208, d134422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133209 q = 0) : d134423 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133209, d134423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133209, d134423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133210 q = 0) : d134424 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133210, d134424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133210, d134424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d133211 q = 0) : d134425 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133211, d134425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133211, d134425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133212 q = 0) : d134426 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133212, d134426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133212, d134426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133213 q = 0) : d134427 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133213, d134427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133213, d134427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11317 (p : Pattern) (selected : d133219 p = 0) : d134433 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133208 q = 0) : d134422 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133208, d134422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11289 q selected
    | true =>
      simp only [d133208, d134422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133209 q = 0) : d134423 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133209, d134423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133209, d134423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133210 q = 0) : d134424 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133210, d134424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133210, d134424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133211 q = 0) : d134425 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133211, d134425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133211, d134425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133212 q = 0) : d134426 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133212, d134426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133212, d134426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133214 q = 0) : d134428 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133214, d134428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11292 q selected
    | true =>
      simp only [d133214, d134428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133215 q = 0) : d134429 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133215, d134429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133215, d134429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133216 q = 0) : d134430 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133216, d134430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133216, d134430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d133217 q = 0) : d134431 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133217, d134431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133217, d134431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133218 q = 0) : d134432 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133218, d134432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133218, d134432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133219 q = 0) : d134433 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133219, d134433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133219, d134433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11318 (p : Pattern) (selected : d133226 p = 0) : d134440 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133195 q = 0) : d134412 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133195, d134412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11311 q selected
    | true =>
      simp only [d133195, d134412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11291 q selected
  have h2 (q : Pattern) (selected : d133198 q = 0) : d134347 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133198, d134347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11312 q selected
    | true =>
      simp only [d133198, d134347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11313 q selected
  have h3 (q : Pattern) (selected : d133199 q = 0) : d134413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133199, d134413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133199, d134413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133201 q = 0) : d134415 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133201, d134415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11314 q selected
    | true =>
      simp only [d133201, d134415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133202 q = 0) : d134416 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133202, d134416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133202, d134416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133203 q = 0) : d134417 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133203, d134417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133203, d134417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133224 q = 0) : d134438 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133224, d134438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133224, d134438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133225 q = 0) : d134439 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133225, d134439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133225, d134439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133226 q = 0) : d134440 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133226, d134440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133226, d134440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11319 (p : Pattern) (selected : d133228 p = 0) : d134442 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133214 q = 0) : d134428 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133214, d134428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11292 q selected
    | true =>
      simp only [d133214, d134428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133215 q = 0) : d134429 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133215, d134429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133215, d134429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133216 q = 0) : d134430 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133216, d134430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133216, d134430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133217 q = 0) : d134431 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133217, d134431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133217, d134431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133218 q = 0) : d134432 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133218, d134432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133218, d134432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133228 q = 0) : d134442 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133228, d134442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133228, d134442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11320 (p : Pattern) (selected : d133235 p = 0) : d134449 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86209 q = 0) : d87456 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86209, d87456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86209, d87456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro364 q selected
  have h2 (q : Pattern) (selected : d86210 q = 0) : d87457 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86210, d87457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86210, d87457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86211 q = 0) : d87458 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86211, d87458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86211, d87458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro365 q selected
  have h4 (q : Pattern) (selected : d86212 q = 0) : d87459 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86212, d87459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86212, d87459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86213 q = 0) : d87460 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86213, d87460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86213, d87460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86217 q = 0) : d87464 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86217, d87464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86217, d87464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro366 q selected
  have h7 (q : Pattern) (selected : d86218 q = 0) : d87465 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86218, d87465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86218, d87465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86219 q = 0) : d87466 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86219, d87466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86219, d87466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133234 q = 0) : d134448 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133234, d134448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133234, d134448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133235 q = 0) : d134449 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133235, d134449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133235, d134449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11321 (p : Pattern) (selected : d133239 p = 0) : d134453 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86211 q = 0) : d87458 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86211, d87458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86211, d87458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro365 q selected
  have h2 (q : Pattern) (selected : d86212 q = 0) : d87459 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86212, d87459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86212, d87459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86217 q = 0) : d87464 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86217, d87464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86217, d87464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro366 q selected
  have h4 (q : Pattern) (selected : d86218 q = 0) : d87465 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86218, d87465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86218, d87465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86219 q = 0) : d87466 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86219, d87466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86219, d87466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86227 q = 0) : d87474 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86227, d87474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86227, d87474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133238 q = 0) : d134452 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133238, d134452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133238, d134452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133239 q = 0) : d134453 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133239, d134453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133239, d134453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11322 (p : Pattern) (selected : d133245 p = 0) : d134459 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133236 q = 0) : d134450 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133236, d134450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11320 q selected
    | true =>
      simp only [d133236, d134450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133237 q = 0) : d134451 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133237, d134451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133237, d134451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133240 q = 0) : d134454 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133240, d134454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11321 q selected
    | true =>
      simp only [d133240, d134454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133241 q = 0) : d134455 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133241, d134455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133241, d134455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133242 q = 0) : d134456 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133242, d134456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133242, d134456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133243 q = 0) : d134457 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133243, d134457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133243, d134457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133244 q = 0) : d134458 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133244, d134458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133244, d134458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133245 q = 0) : d134459 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133245, d134459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133245, d134459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11323 (p : Pattern) (selected : d133247 p = 0) : d134461 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86217 q = 0) : d87464 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86217, d87464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86217, d87464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro366 q selected
  have h2 (q : Pattern) (selected : d86218 q = 0) : d87465 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86218, d87465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86218, d87465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86227 q = 0) : d87474 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86227, d87474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86227, d87474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133246 q = 0) : d134460 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133246, d134460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133246, d134460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133247 q = 0) : d134461 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133247, d134461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133247, d134461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11324 (p : Pattern) (selected : d133253 p = 0) : d134467 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133240 q = 0) : d134454 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133240, d134454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11321 q selected
    | true =>
      simp only [d133240, d134454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133241 q = 0) : d134455 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133241, d134455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133241, d134455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133248 q = 0) : d134462 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133248, d134462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11323 q selected
    | true =>
      simp only [d133248, d134462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133249 q = 0) : d134463 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133249, d134463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133249, d134463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133250 q = 0) : d134464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133250, d134464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133250, d134464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133251 q = 0) : d134465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133251, d134465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133251, d134465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133252 q = 0) : d134466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133252, d134466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133252, d134466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133253 q = 0) : d134467 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133253, d134467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133253, d134467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11325 (p : Pattern) (selected : d133256 p = 0) : d134453 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86236 q = 0) : d87458 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86236, d87458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86236, d87458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro373 q selected
  have h2 (q : Pattern) (selected : d86237 q = 0) : d87459 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86237, d87459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86237, d87459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86238 q = 0) : d87464 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86238, d87464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86238, d87464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro374 q selected
  have h4 (q : Pattern) (selected : d86239 q = 0) : d87465 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86239, d87465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86239, d87465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86240 q = 0) : d87466 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86240, d87466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86240, d87466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86244 q = 0) : d87474 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86244, d87474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86244, d87474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133255 q = 0) : d134452 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133255, d134452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133255, d134452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133256 q = 0) : d134453 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133256, d134453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133256, d134453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11326 (p : Pattern) (selected : d133260 p = 0) : d134461 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86238 q = 0) : d87464 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86238, d87464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86238, d87464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro374 q selected
  have h2 (q : Pattern) (selected : d86239 q = 0) : d87465 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86239, d87465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86239, d87465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86244 q = 0) : d87474 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86244, d87474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86244, d87474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133259 q = 0) : d134460 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133259, d134460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133259, d134460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133260 q = 0) : d134461 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133260, d134461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133260, d134461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11327 (p : Pattern) (selected : d133266 p = 0) : d134467 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133257 q = 0) : d134454 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133257, d134454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11325 q selected
    | true =>
      simp only [d133257, d134454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133258 q = 0) : d134455 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133258, d134455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133258, d134455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133261 q = 0) : d134462 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133261, d134462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11326 q selected
    | true =>
      simp only [d133261, d134462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133262 q = 0) : d134463 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133262, d134463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133262, d134463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133263 q = 0) : d134464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133263, d134464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133263, d134464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133264 q = 0) : d134465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133264, d134465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133264, d134465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133265 q = 0) : d134466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133265, d134466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133265, d134466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133266 q = 0) : d134467 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133266, d134467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133266, d134467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11328 (p : Pattern) (selected : d133270 p = 0) : d134472 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133261 q = 0) : d134462 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133261, d134462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11326 q selected
    | true =>
      simp only [d133261, d134462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133262 q = 0) : d134463 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133262, d134463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133262, d134463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133267 q = 0) : d134469 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133267, d134469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133267, d134469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133268 q = 0) : d134470 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133268, d134470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133268, d134470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133269 q = 0) : d134471 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133269, d134471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133269, d134471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133270 q = 0) : d134472 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133270, d134472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133270, d134472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11329 (p : Pattern) (selected : d133277 p = 0) : d134479 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86211 q = 0) : d87458 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86211, d87458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86211, d87458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro365 q selected
  have h2 (q : Pattern) (selected : d86212 q = 0) : d87459 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86212, d87459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86212, d87459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86217 q = 0) : d87464 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86217, d87464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86217, d87464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro366 q selected
  have h4 (q : Pattern) (selected : d86218 q = 0) : d87465 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86218, d87465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86218, d87465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86219 q = 0) : d87466 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86219, d87466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86219, d87466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133273 q = 0) : d134475 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d133273, d134475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133273, d134475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3364 q selected
  have h7 (q : Pattern) (selected : d133274 q = 0) : d134476 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d133274, d134476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133274, d134476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133275 q = 0) : d134477 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d133275, d134477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133275, d134477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d133276 q = 0) : d134478 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133276, d134478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133276, d134478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133277 q = 0) : d134479 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133277, d134479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133277, d134479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11330 (p : Pattern) (selected : d133283 p = 0) : d134485 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133278 q = 0) : d134480 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133278, d134480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11329 q selected
    | true =>
      simp only [d133278, d134480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133279 q = 0) : d134481 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133279, d134481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133279, d134481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133280 q = 0) : d134482 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133280, d134482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133280, d134482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133281 q = 0) : d134483 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133281, d134483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133281, d134483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133282 q = 0) : d134484 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133282, d134484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133282, d134484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133283 q = 0) : d134485 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133283, d134485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133283, d134485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11331 (p : Pattern) (selected : d133289 p = 0) : d134491 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133254 q = 0) : d134468 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133254, d134468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11322 q selected
    | true =>
      simp only [d133254, d134468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11324 q selected
  have h2 (q : Pattern) (selected : d133271 q = 0) : d134473 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133271, d134473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11327 q selected
    | true =>
      simp only [d133271, d134473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11328 q selected
  have h3 (q : Pattern) (selected : d133272 q = 0) : d134474 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133272, d134474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133272, d134474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133284 q = 0) : d134486 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133284, d134486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11330 q selected
    | true =>
      simp only [d133284, d134486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133285 q = 0) : d134487 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133285, d134487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133285, d134487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133286 q = 0) : d134488 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133286, d134488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133286, d134488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133287 q = 0) : d134489 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133287, d134489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133287, d134489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133288 q = 0) : d134490 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133288, d134490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133288, d134490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133289 q = 0) : d134491 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133289, d134491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133289, d134491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11332 (p : Pattern) (selected : d133294 p = 0) : d134472 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133248 q = 0) : d134462 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133248, d134462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11323 q selected
    | true =>
      simp only [d133248, d134462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133249 q = 0) : d134463 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133249, d134463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133249, d134463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133291 q = 0) : d134469 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133291, d134469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133291, d134469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133292 q = 0) : d134470 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133292, d134470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133292, d134470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133293 q = 0) : d134471 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133293, d134471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133293, d134471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133294 q = 0) : d134472 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133294, d134472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133294, d134472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11333 (p : Pattern) (selected : d133300 p = 0) : d134498 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133295 q = 0) : d134493 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133295, d134493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11332 q selected
    | true =>
      simp only [d133295, d134493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133296 q = 0) : d134494 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133296, d134494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133296, d134494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133297 q = 0) : d134495 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133297, d134495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133297, d134495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133298 q = 0) : d134496 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133298, d134496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133298, d134496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133299 q = 0) : d134497 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133299, d134497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133299, d134497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133300 q = 0) : d134498 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133300, d134498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133300, d134498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11334 (p : Pattern) (selected : d133306 p = 0) : d134504 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133109 q = 0) : d134343 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133109, d134343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133109, d134343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11290 q selected
  have h2 (q : Pattern) (selected : d133110 q = 0) : d134344 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133110, d134344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133110, d134344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d133119 q = 0) : d134353 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133119, d134353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11290 q selected
    | true =>
      simp only [d133119, d134353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11293 q selected
  have h4 (q : Pattern) (selected : d133120 q = 0) : d134354 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133120, d134354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133120, d134354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133121 q = 0) : d134355 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133121, d134355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133121, d134355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133207 q = 0) : d134421 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133207, d134421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11306 q selected
    | true =>
      simp only [d133207, d134421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11315 q selected
  have h7 (q : Pattern) (selected : d133220 q = 0) : d134434 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133220, d134434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11316 q selected
    | true =>
      simp only [d133220, d134434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11317 q selected
  have h8 (q : Pattern) (selected : d133221 q = 0) : d134435 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133221, d134435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133221, d134435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133222 q = 0) : d134436 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133222, d134436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d133222, d134436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d133223 q = 0) : d134437 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133223, d134437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133223, d134437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133227 q = 0) : d134441 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133227, d134441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133227, d134441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11318 q selected
  have h12 (q : Pattern) (selected : d133229 q = 0) : d134443 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133229, d134443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133229, d134443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11319 q selected
  have h13 (q : Pattern) (selected : d133230 q = 0) : d134444 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133230, d134444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d133230, d134444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d133231 q = 0) : d134445 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133231, d134445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d133231, d134445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d133232 q = 0) : d134446 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133232, d134446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d133232, d134446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d133233 q = 0) : d134447 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d133233, d134447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133233, d134447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d133290 q = 0) : d134492 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133290, d134492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133290, d134492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11331 q selected
  have h18 (q : Pattern) (selected : d133301 q = 0) : d134499 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133301, d134499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133301, d134499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11333 q selected
  have h19 (q : Pattern) (selected : d133302 q = 0) : d134500 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133302, d134500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d133302, d134500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d133303 q = 0) : d134501 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133303, d134501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d133303, d134501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d133304 q = 0) : d134502 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133304, d134502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d133304, d134502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d133305 q = 0) : d134503 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d133305, d134503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d133305, d134503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d133306 q = 0) : d134504 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d133306, d134504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d133306, d134504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro11335 (p : Pattern) (selected : d133312 p = 0) : d134510 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133307 q = 0) : d134505 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d133307, d134505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133307, d134505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11334 q selected
  have h2 (q : Pattern) (selected : d133308 q = 0) : d134506 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d133308, d134506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133308, d134506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133309 q = 0) : d134507 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d133309, d134507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133309, d134507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133310 q = 0) : d134508 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d133310, d134508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133310, d134508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133311 q = 0) : d134509 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d133311, d134509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133311, d134509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133312 q = 0) : d134510 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d133312, d134510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133312, d134510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11336 (p : Pattern) (selected : d133316 p = 0) : d134514 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86293 q = 0) : d87520 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86293, d87520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86293, d87520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro390 q selected
  have h2 (q : Pattern) (selected : d86294 q = 0) : d87521 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86294, d87521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86294, d87521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86295 q = 0) : d87522 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86295, d87522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86295, d87522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro392 q selected
  have h4 (q : Pattern) (selected : d86296 q = 0) : d87523 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86296, d87523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86296, d87523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86297 q = 0) : d87524 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86297, d87524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86297, d87524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86301 q = 0) : d87528 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86301, d87528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86301, d87528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133315 q = 0) : d134513 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133315, d134513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133315, d134513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133316 q = 0) : d134514 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133316, d134514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133316, d134514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11337 (p : Pattern) (selected : d133320 p = 0) : d134518 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86295 q = 0) : d87522 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86295, d87522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86295, d87522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro392 q selected
  have h2 (q : Pattern) (selected : d86296 q = 0) : d87523 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86296, d87523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86296, d87523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86301 q = 0) : d87528 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86301, d87528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86301, d87528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133319 q = 0) : d134517 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133319, d134517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133319, d134517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133320 q = 0) : d134518 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133320, d134518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133320, d134518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11338 (p : Pattern) (selected : d133326 p = 0) : d134524 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133317 q = 0) : d134515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133317, d134515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11336 q selected
    | true =>
      simp only [d133317, d134515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133318 q = 0) : d134516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133318, d134516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133318, d134516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133321 q = 0) : d134519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11337 q selected
    | true =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133322 q = 0) : d134520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133323 q = 0) : d134521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133323, d134521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133323, d134521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133324 q = 0) : d134522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133324, d134522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133324, d134522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133325 q = 0) : d134523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133325, d134523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133325, d134523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133326 q = 0) : d134524 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133326, d134524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133326, d134524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11339 (p : Pattern) (selected : d133330 p = 0) : d134528 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133321 q = 0) : d134519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11337 q selected
    | true =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133322 q = 0) : d134520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133327 q = 0) : d134525 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133327, d134525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133327, d134525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133328 q = 0) : d134526 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133328, d134526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133328, d134526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133329 q = 0) : d134527 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133329, d134527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133329, d134527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133330 q = 0) : d134528 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133330, d134528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133330, d134528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11340 (p : Pattern) (selected : d133336 p = 0) : d134534 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133331 q = 0) : d134529 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133331, d134529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11338 q selected
    | true =>
      simp only [d133331, d134529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11339 q selected
  have h2 (q : Pattern) (selected : d133332 q = 0) : d134530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133332, d134530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133332, d134530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133333 q = 0) : d134531 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133333, d134531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133333, d134531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133334 q = 0) : d134532 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133334, d134532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133334, d134532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133335 q = 0) : d134533 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133335, d134533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133335, d134533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133336 q = 0) : d134534 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133336, d134534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133336, d134534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11341 (p : Pattern) (selected : d133339 p = 0) : d134537 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133317 q = 0) : d134515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133317, d134515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11336 q selected
    | true =>
      simp only [d133317, d134515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133318 q = 0) : d134516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133318, d134516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133318, d134516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133321 q = 0) : d134519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11337 q selected
    | true =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133322 q = 0) : d134520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133323 q = 0) : d134521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133323, d134521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133323, d134521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133324 q = 0) : d134522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133324, d134522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133324, d134522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133325 q = 0) : d134523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133325, d134523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133325, d134523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133339 q = 0) : d134537 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133339, d134537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133339, d134537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11342 (p : Pattern) (selected : d133340 p = 0) : d134538 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133321 q = 0) : d134519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11337 q selected
    | true =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133322 q = 0) : d134520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133327 q = 0) : d134525 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133327, d134525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133327, d134525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133328 q = 0) : d134526 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133328, d134526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133328, d134526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133329 q = 0) : d134527 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133329, d134527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133329, d134527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133340 q = 0) : d134538 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133340, d134538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133340, d134538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11343 (p : Pattern) (selected : d133346 p = 0) : d134544 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133331 q = 0) : d134529 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133331, d134529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11338 q selected
    | true =>
      simp only [d133331, d134529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11339 q selected
  have h2 (q : Pattern) (selected : d133332 q = 0) : d134530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133332, d134530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133332, d134530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133333 q = 0) : d134531 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133333, d134531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133333, d134531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133334 q = 0) : d134532 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133334, d134532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133334, d134532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133335 q = 0) : d134533 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133335, d134533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133335, d134533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133341 q = 0) : d134539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133341, d134539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11341 q selected
    | true =>
      simp only [d133341, d134539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11342 q selected
  have h7 (q : Pattern) (selected : d133342 q = 0) : d134540 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133342, d134540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133342, d134540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133343 q = 0) : d134541 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133343, d134541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133343, d134541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d133344 q = 0) : d134542 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133344, d134542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133344, d134542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133345 q = 0) : d134543 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133345, d134543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133345, d134543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133346 q = 0) : d134544 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133346, d134544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133346, d134544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11344 (p : Pattern) (selected : d133351 p = 0) : d134549 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133317 q = 0) : d134515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133317, d134515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11336 q selected
    | true =>
      simp only [d133317, d134515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133318 q = 0) : d134516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133318, d134516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133318, d134516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133321 q = 0) : d134519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11337 q selected
    | true =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133322 q = 0) : d134520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133323 q = 0) : d134521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133323, d134521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133323, d134521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133324 q = 0) : d134522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133324, d134522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133324, d134522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133350 q = 0) : d134548 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133350, d134548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133350, d134548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133351 q = 0) : d134549 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133351, d134549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133351, d134549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11345 (p : Pattern) (selected : d133353 p = 0) : d134551 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133321 q = 0) : d134519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11337 q selected
    | true =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133322 q = 0) : d134520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133327 q = 0) : d134525 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133327, d134525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133327, d134525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133328 q = 0) : d134526 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133328, d134526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133328, d134526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133352 q = 0) : d134550 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133352, d134550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133352, d134550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133353 q = 0) : d134551 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133353, d134551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133353, d134551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11346 (p : Pattern) (selected : d133360 p = 0) : d134558 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133317 q = 0) : d134515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133317, d134515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11336 q selected
    | true =>
      simp only [d133317, d134515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133318 q = 0) : d134516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133318, d134516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133318, d134516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133321 q = 0) : d134519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11337 q selected
    | true =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133322 q = 0) : d134520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133323 q = 0) : d134521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133323, d134521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133323, d134521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133358 q = 0) : d134556 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133358, d134556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133358, d134556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133359 q = 0) : d134557 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133359, d134557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133359, d134557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133360 q = 0) : d134558 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133360, d134558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133360, d134558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11347 (p : Pattern) (selected : d133363 p = 0) : d134561 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133321 q = 0) : d134519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11337 q selected
    | true =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133322 q = 0) : d134520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133327 q = 0) : d134525 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133327, d134525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133327, d134525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133361 q = 0) : d134559 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133361, d134559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133361, d134559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133362 q = 0) : d134560 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133362, d134560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133362, d134560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133363 q = 0) : d134561 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133363, d134561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133363, d134561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11348 (p : Pattern) (selected : d133368 p = 0) : d134566 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86349 q = 0) : d87576 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86349, d87576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86349, d87576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro389 q selected
  have h2 (q : Pattern) (selected : d86350 q = 0) : d87577 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86350, d87577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86350, d87577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86293 q = 0) : d87520 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86293, d87520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86293, d87520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro390 q selected
  have h4 (q : Pattern) (selected : d86294 q = 0) : d87521 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86294, d87521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86294, d87521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86351 q = 0) : d87578 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86351, d87578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86351, d87578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86295 q = 0) : d87522 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86295, d87522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86295, d87522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro392 q selected
  have h7 (q : Pattern) (selected : d86296 q = 0) : d87523 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86296, d87523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86296, d87523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86297 q = 0) : d87524 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86297, d87524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86297, d87524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133367 q = 0) : d134565 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133367, d134565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133367, d134565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133368 q = 0) : d134566 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133368, d134566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133368, d134566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11349 (p : Pattern) (selected : d133374 p = 0) : d134572 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133369 q = 0) : d134567 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133369, d134567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11348 q selected
    | true =>
      simp only [d133369, d134567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133370 q = 0) : d134568 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133370, d134568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133370, d134568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133317 q = 0) : d134515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133317, d134515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11336 q selected
    | true =>
      simp only [d133317, d134515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133318 q = 0) : d134516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133318, d134516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133318, d134516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133371 q = 0) : d134569 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133371, d134569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133371, d134569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133372 q = 0) : d134570 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133372, d134570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133372, d134570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133373 q = 0) : d134571 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133373, d134571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133373, d134571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133374 q = 0) : d134572 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133374, d134572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133374, d134572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11350 (p : Pattern) (selected : d133377 p = 0) : d134514 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86360 q = 0) : d87520 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86360, d87520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86360, d87520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro419 q selected
  have h2 (q : Pattern) (selected : d86361 q = 0) : d87521 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86361, d87521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86361, d87521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86362 q = 0) : d87522 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86362, d87522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86362, d87522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro421 q selected
  have h4 (q : Pattern) (selected : d86363 q = 0) : d87523 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86363, d87523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86363, d87523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86364 q = 0) : d87524 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86364, d87524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86364, d87524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86368 q = 0) : d87528 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86368, d87528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86368, d87528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133376 q = 0) : d134513 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133376, d134513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133376, d134513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133377 q = 0) : d134514 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133377, d134514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133377, d134514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11351 (p : Pattern) (selected : d133381 p = 0) : d134518 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86362 q = 0) : d87522 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86362, d87522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86362, d87522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro421 q selected
  have h2 (q : Pattern) (selected : d86363 q = 0) : d87523 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86363, d87523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86363, d87523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86368 q = 0) : d87528 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86368, d87528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86368, d87528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133380 q = 0) : d134517 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133380, d134517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133380, d134517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133381 q = 0) : d134518 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133381, d134518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133381, d134518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11352 (p : Pattern) (selected : d133387 p = 0) : d134524 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133378 q = 0) : d134515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133378, d134515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11350 q selected
    | true =>
      simp only [d133378, d134515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133379 q = 0) : d134516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133379, d134516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133379, d134516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133382 q = 0) : d134519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133382, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11351 q selected
    | true =>
      simp only [d133382, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133383 q = 0) : d134520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133383, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133383, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133384 q = 0) : d134521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133384, d134521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133384, d134521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133385 q = 0) : d134522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133385, d134522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133385, d134522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133386 q = 0) : d134523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133386, d134523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133386, d134523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133387 q = 0) : d134524 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133387, d134524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133387, d134524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11353 (p : Pattern) (selected : d133391 p = 0) : d134528 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133382 q = 0) : d134519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133382, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11351 q selected
    | true =>
      simp only [d133382, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133383 q = 0) : d134520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133383, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133383, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133388 q = 0) : d134525 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133388, d134525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133388, d134525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133389 q = 0) : d134526 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133389, d134526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133389, d134526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133390 q = 0) : d134527 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133390, d134527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133390, d134527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133391 q = 0) : d134528 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133391, d134528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133391, d134528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11354 (p : Pattern) (selected : d133398 p = 0) : d134579 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86293 q = 0) : d87520 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86293, d87520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86293, d87520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro390 q selected
  have h2 (q : Pattern) (selected : d86294 q = 0) : d87521 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86294, d87521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86294, d87521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86295 q = 0) : d87522 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86295, d87522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86295, d87522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro392 q selected
  have h4 (q : Pattern) (selected : d86296 q = 0) : d87523 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86296, d87523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86296, d87523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86297 q = 0) : d87524 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86297, d87524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86297, d87524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133394 q = 0) : d134575 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d133394, d134575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133394, d134575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3372 q selected
  have h7 (q : Pattern) (selected : d133395 q = 0) : d134576 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d133395, d134576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133395, d134576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133396 q = 0) : d134577 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d133396, d134577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133396, d134577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d133397 q = 0) : d134578 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133397, d134578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133397, d134578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133398 q = 0) : d134579 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133398, d134579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133398, d134579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11355 (p : Pattern) (selected : d133404 p = 0) : d134585 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133399 q = 0) : d134580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133399, d134580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11354 q selected
    | true =>
      simp only [d133399, d134580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133400 q = 0) : d134581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133400, d134581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133400, d134581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133401 q = 0) : d134582 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133401, d134582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133401, d134582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133402 q = 0) : d134583 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133402, d134583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133402, d134583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133403 q = 0) : d134584 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133403, d134584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133403, d134584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133404 q = 0) : d134585 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133404, d134585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133404, d134585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11356 (p : Pattern) (selected : d133410 p = 0) : d134591 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133354 q = 0) : d134552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133354, d134552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11344 q selected
    | true =>
      simp only [d133354, d134552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11345 q selected
  have h2 (q : Pattern) (selected : d133355 q = 0) : d134553 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133355, d134553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133355, d134553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133356 q = 0) : d134554 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133356, d134554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133356, d134554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133357 q = 0) : d134555 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133357, d134555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133357, d134555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133364 q = 0) : d134562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133364, d134562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11346 q selected
    | true =>
      simp only [d133364, d134562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11347 q selected
  have h6 (q : Pattern) (selected : d133365 q = 0) : d134563 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133365, d134563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133365, d134563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133366 q = 0) : d134564 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133366, d134564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133366, d134564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133375 q = 0) : d134573 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133375, d134573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11349 q selected
    | true =>
      simp only [d133375, d134573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11338 q selected
  have h9 (q : Pattern) (selected : d133392 q = 0) : d134529 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133392, d134529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11352 q selected
    | true =>
      simp only [d133392, d134529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11353 q selected
  have h10 (q : Pattern) (selected : d133393 q = 0) : d134574 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133393, d134574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d133393, d134574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133405 q = 0) : d134586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133405, d134586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11355 q selected
    | true =>
      simp only [d133405, d134586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d133406 q = 0) : d134587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133406, d134587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d133406, d134587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d133407 q = 0) : d134588 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133407, d134588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133407, d134588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d133408 q = 0) : d134589 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133408, d134589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133408, d134589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d133409 q = 0) : d134590 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133409, d134590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133409, d134590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d133410 q = 0) : d134591 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133410, d134591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133410, d134591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro11357 (p : Pattern) (selected : d133411 p = 0) : d134592 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133317 q = 0) : d134515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133317, d134515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11336 q selected
    | true =>
      simp only [d133317, d134515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133318 q = 0) : d134516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133318, d134516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133318, d134516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133321 q = 0) : d134519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11337 q selected
    | true =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133322 q = 0) : d134520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133323 q = 0) : d134521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133323, d134521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133323, d134521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133324 q = 0) : d134522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133324, d134522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133324, d134522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133350 q = 0) : d134548 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133350, d134548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133350, d134548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133411 q = 0) : d134592 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133411, d134592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133411, d134592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11358 (p : Pattern) (selected : d133412 p = 0) : d134593 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133321 q = 0) : d134519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11337 q selected
    | true =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133322 q = 0) : d134520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133327 q = 0) : d134525 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133327, d134525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133327, d134525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133328 q = 0) : d134526 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133328, d134526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133328, d134526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133352 q = 0) : d134550 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133352, d134550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133352, d134550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133412 q = 0) : d134593 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133412, d134593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133412, d134593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11359 (p : Pattern) (selected : d133417 p = 0) : d134598 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133317 q = 0) : d134515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133317, d134515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11336 q selected
    | true =>
      simp only [d133317, d134515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133318 q = 0) : d134516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133318, d134516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133318, d134516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133321 q = 0) : d134519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11337 q selected
    | true =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133322 q = 0) : d134520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133323 q = 0) : d134521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133323, d134521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133323, d134521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133358 q = 0) : d134556 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133358, d134556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133358, d134556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133359 q = 0) : d134557 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133359, d134557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133359, d134557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133417 q = 0) : d134598 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133417, d134598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133417, d134598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11360 (p : Pattern) (selected : d133418 p = 0) : d134599 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133321 q = 0) : d134519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11337 q selected
    | true =>
      simp only [d133321, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133322 q = 0) : d134520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133322, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133327 q = 0) : d134525 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133327, d134525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133327, d134525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133361 q = 0) : d134559 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133361, d134559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133361, d134559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133362 q = 0) : d134560 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133362, d134560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133362, d134560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133418 q = 0) : d134599 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133418, d134599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133418, d134599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11361 (p : Pattern) (selected : d133422 p = 0) : d134603 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133369 q = 0) : d134567 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133369, d134567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11348 q selected
    | true =>
      simp only [d133369, d134567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133370 q = 0) : d134568 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133370, d134568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133370, d134568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133317 q = 0) : d134515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133317, d134515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11336 q selected
    | true =>
      simp only [d133317, d134515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133318 q = 0) : d134516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133318, d134516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133318, d134516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133371 q = 0) : d134569 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133371, d134569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133371, d134569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133372 q = 0) : d134570 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133372, d134570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133372, d134570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133373 q = 0) : d134571 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133373, d134571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133373, d134571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133422 q = 0) : d134603 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133422, d134603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133422, d134603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11362 (p : Pattern) (selected : d133424 p = 0) : d134537 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133378 q = 0) : d134515 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133378, d134515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11350 q selected
    | true =>
      simp only [d133378, d134515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133379 q = 0) : d134516 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133379, d134516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133379, d134516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133382 q = 0) : d134519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133382, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11351 q selected
    | true =>
      simp only [d133382, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133383 q = 0) : d134520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133383, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133383, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133384 q = 0) : d134521 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133384, d134521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133384, d134521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133385 q = 0) : d134522 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133385, d134522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133385, d134522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133386 q = 0) : d134523 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133386, d134523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133386, d134523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133424 q = 0) : d134537 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133424, d134537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133424, d134537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11363 (p : Pattern) (selected : d133425 p = 0) : d134538 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133382 q = 0) : d134519 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133382, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11351 q selected
    | true =>
      simp only [d133382, d134519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133383 q = 0) : d134520 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133383, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133383, d134520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133388 q = 0) : d134525 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133388, d134525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133388, d134525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133389 q = 0) : d134526 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133389, d134526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133389, d134526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133390 q = 0) : d134527 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133390, d134527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133390, d134527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133425 q = 0) : d134538 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133425, d134538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133425, d134538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11364 (p : Pattern) (selected : d133428 p = 0) : d134606 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133399 q = 0) : d134580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133399, d134580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11354 q selected
    | true =>
      simp only [d133399, d134580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133400 q = 0) : d134581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133400, d134581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133400, d134581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133401 q = 0) : d134582 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133401, d134582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133401, d134582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133402 q = 0) : d134583 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133402, d134583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133402, d134583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133403 q = 0) : d134584 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133403, d134584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133403, d134584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133428 q = 0) : d134606 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133428, d134606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133428, d134606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11365 (p : Pattern) (selected : d133434 p = 0) : d134612 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133354 q = 0) : d134552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133354, d134552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11344 q selected
    | true =>
      simp only [d133354, d134552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11345 q selected
  have h2 (q : Pattern) (selected : d133355 q = 0) : d134553 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133355, d134553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133355, d134553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133356 q = 0) : d134554 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133356, d134554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133356, d134554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133357 q = 0) : d134555 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133357, d134555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133357, d134555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133364 q = 0) : d134562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133364, d134562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11346 q selected
    | true =>
      simp only [d133364, d134562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11347 q selected
  have h6 (q : Pattern) (selected : d133365 q = 0) : d134563 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133365, d134563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133365, d134563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133366 q = 0) : d134564 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133366, d134564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133366, d134564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133375 q = 0) : d134573 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133375, d134573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11349 q selected
    | true =>
      simp only [d133375, d134573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11338 q selected
  have h9 (q : Pattern) (selected : d133392 q = 0) : d134529 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133392, d134529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11352 q selected
    | true =>
      simp only [d133392, d134529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11353 q selected
  have h10 (q : Pattern) (selected : d133393 q = 0) : d134574 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133393, d134574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d133393, d134574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133405 q = 0) : d134586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133405, d134586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11355 q selected
    | true =>
      simp only [d133405, d134586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d133406 q = 0) : d134587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133406, d134587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d133406, d134587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d133407 q = 0) : d134588 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133407, d134588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133407, d134588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d133408 q = 0) : d134589 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133408, d134589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133408, d134589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d133409 q = 0) : d134590 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133409, d134590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133409, d134590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d133413 q = 0) : d134594 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133413, d134594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11357 q selected
    | true =>
      simp only [d133413, d134594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11358 q selected
  have h17 (q : Pattern) (selected : d133414 q = 0) : d134595 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133414, d134595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133414, d134595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d133415 q = 0) : d134596 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133415, d134596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d133415, d134596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d133416 q = 0) : d134597 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133416, d134597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133416, d134597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d133419 q = 0) : d134600 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133419, d134600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11359 q selected
    | true =>
      simp only [d133419, d134600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11360 q selected
  have h21 (q : Pattern) (selected : d133420 q = 0) : d134601 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133420, d134601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133420, d134601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d133421 q = 0) : d134602 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133421, d134602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d133421, d134602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d133423 q = 0) : d134604 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133423, d134604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11361 q selected
    | true =>
      simp only [d133423, d134604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11341 q selected
  have h24 (q : Pattern) (selected : d133426 q = 0) : d134539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133426, d134539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11362 q selected
    | true =>
      simp only [d133426, d134539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11363 q selected
  have h25 (q : Pattern) (selected : d133427 q = 0) : d134605 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133427, d134605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d133427, d134605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d133429 q = 0) : d134607 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133429, d134607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11364 q selected
    | true =>
      simp only [d133429, d134607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d133430 q = 0) : d134608 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133430, d134608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d133430, d134608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d133431 q = 0) : d134609 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133431, d134609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d133431, d134609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d133432 q = 0) : d134610 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133432, d134610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d133432, d134610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d133433 q = 0) : d134611 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133433, d134611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d133433, d134611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d133434 q = 0) : d134612 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133434, d134612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d133434, d134612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro11366 (p : Pattern) (selected : d133441 p = 0) : d134619 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133331 q = 0) : d134529 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133331, d134529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11338 q selected
    | true =>
      simp only [d133331, d134529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11339 q selected
  have h2 (q : Pattern) (selected : d133332 q = 0) : d134530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133332, d134530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133332, d134530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133333 q = 0) : d134531 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133333, d134531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133333, d134531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133334 q = 0) : d134532 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133334, d134532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133334, d134532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133335 q = 0) : d134533 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133335, d134533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133335, d134533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133436 q = 0) : d134614 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133436, d134614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11339 q selected
    | true =>
      simp only [d133436, d134614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133437 q = 0) : d134615 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133437, d134615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133437, d134615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133438 q = 0) : d134616 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133438, d134616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133438, d134616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d133439 q = 0) : d134617 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133439, d134617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133439, d134617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133440 q = 0) : d134618 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133440, d134618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133440, d134618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133441 q = 0) : d134619 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133441, d134619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133441, d134619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11367 (p : Pattern) (selected : d133447 p = 0) : d134625 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133436 q = 0) : d134614 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133436, d134614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11339 q selected
    | true =>
      simp only [d133436, d134614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133437 q = 0) : d134615 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133437, d134615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133437, d134615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133438 q = 0) : d134616 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133438, d134616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133438, d134616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133439 q = 0) : d134617 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133439, d134617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133439, d134617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133440 q = 0) : d134618 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133440, d134618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133440, d134618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133442 q = 0) : d134620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133442, d134620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11342 q selected
    | true =>
      simp only [d133442, d134620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133443 q = 0) : d134621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133443, d134621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133443, d134621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133444 q = 0) : d134622 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133444, d134622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133444, d134622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d133445 q = 0) : d134623 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133445, d134623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133445, d134623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133446 q = 0) : d134624 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133446, d134624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133446, d134624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133447 q = 0) : d134625 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133447, d134625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133447, d134625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11368 (p : Pattern) (selected : d133454 p = 0) : d134632 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133423 q = 0) : d134604 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133423, d134604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11361 q selected
    | true =>
      simp only [d133423, d134604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11341 q selected
  have h2 (q : Pattern) (selected : d133426 q = 0) : d134539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133426, d134539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11362 q selected
    | true =>
      simp only [d133426, d134539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11363 q selected
  have h3 (q : Pattern) (selected : d133427 q = 0) : d134605 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133427, d134605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133427, d134605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133429 q = 0) : d134607 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133429, d134607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11364 q selected
    | true =>
      simp only [d133429, d134607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133430 q = 0) : d134608 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133430, d134608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133430, d134608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133431 q = 0) : d134609 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133431, d134609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133431, d134609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133452 q = 0) : d134630 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133452, d134630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133452, d134630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133453 q = 0) : d134631 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133453, d134631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133453, d134631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133454 q = 0) : d134632 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133454, d134632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133454, d134632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11369 (p : Pattern) (selected : d133456 p = 0) : d134634 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133442 q = 0) : d134620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133442, d134620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11342 q selected
    | true =>
      simp only [d133442, d134620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133443 q = 0) : d134621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133443, d134621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133443, d134621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133444 q = 0) : d134622 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133444, d134622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133444, d134622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133445 q = 0) : d134623 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133445, d134623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133445, d134623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133446 q = 0) : d134624 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133446, d134624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133446, d134624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133456 q = 0) : d134634 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133456, d134634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133456, d134634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11370 (p : Pattern) (selected : d133463 p = 0) : d134641 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86443 q = 0) : d87646 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86443, d87646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86443, d87646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro440 q selected
  have h2 (q : Pattern) (selected : d86444 q = 0) : d87647 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86444, d87647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86444, d87647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86445 q = 0) : d87648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86445, d87648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86445, d87648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro441 q selected
  have h4 (q : Pattern) (selected : d86446 q = 0) : d87649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86446, d87649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86446, d87649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86447 q = 0) : d87650 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86447, d87650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86447, d87650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86451 q = 0) : d87654 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86451, d87654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86451, d87654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro442 q selected
  have h7 (q : Pattern) (selected : d86452 q = 0) : d87655 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86452, d87655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86452, d87655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86453 q = 0) : d87656 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86453, d87656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86453, d87656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133462 q = 0) : d134640 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133462, d134640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133462, d134640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133463 q = 0) : d134641 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133463, d134641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133463, d134641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11371 (p : Pattern) (selected : d133467 p = 0) : d134645 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86445 q = 0) : d87648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86445, d87648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86445, d87648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro441 q selected
  have h2 (q : Pattern) (selected : d86446 q = 0) : d87649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86446, d87649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86446, d87649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86451 q = 0) : d87654 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86451, d87654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86451, d87654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro442 q selected
  have h4 (q : Pattern) (selected : d86452 q = 0) : d87655 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86452, d87655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86452, d87655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86453 q = 0) : d87656 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86453, d87656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86453, d87656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86461 q = 0) : d87664 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86461, d87664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86461, d87664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133466 q = 0) : d134644 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133466, d134644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133466, d134644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133467 q = 0) : d134645 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133467, d134645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133467, d134645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11372 (p : Pattern) (selected : d133473 p = 0) : d134651 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133464 q = 0) : d134642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133464, d134642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11370 q selected
    | true =>
      simp only [d133464, d134642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133465 q = 0) : d134643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133465, d134643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133465, d134643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133468 q = 0) : d134646 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133468, d134646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11371 q selected
    | true =>
      simp only [d133468, d134646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133469 q = 0) : d134647 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133469, d134647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133469, d134647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133470 q = 0) : d134648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133470, d134648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133470, d134648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133471 q = 0) : d134649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133471, d134649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133471, d134649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133472 q = 0) : d134650 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133472, d134650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133472, d134650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133473 q = 0) : d134651 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133473, d134651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133473, d134651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11373 (p : Pattern) (selected : d133475 p = 0) : d134653 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86451 q = 0) : d87654 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86451, d87654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86451, d87654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro442 q selected
  have h2 (q : Pattern) (selected : d86452 q = 0) : d87655 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86452, d87655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86452, d87655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86461 q = 0) : d87664 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86461, d87664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86461, d87664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133474 q = 0) : d134652 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133474, d134652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133474, d134652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133475 q = 0) : d134653 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133475, d134653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133475, d134653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11374 (p : Pattern) (selected : d133481 p = 0) : d134659 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133468 q = 0) : d134646 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133468, d134646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11371 q selected
    | true =>
      simp only [d133468, d134646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133469 q = 0) : d134647 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133469, d134647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133469, d134647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133476 q = 0) : d134654 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133476, d134654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11373 q selected
    | true =>
      simp only [d133476, d134654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133477 q = 0) : d134655 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133477, d134655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133477, d134655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133478 q = 0) : d134656 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133478, d134656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133478, d134656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133479 q = 0) : d134657 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133479, d134657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133479, d134657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133480 q = 0) : d134658 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133480, d134658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133480, d134658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133481 q = 0) : d134659 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133481, d134659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133481, d134659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11375 (p : Pattern) (selected : d133484 p = 0) : d134645 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86470 q = 0) : d87648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86470, d87648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86470, d87648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro449 q selected
  have h2 (q : Pattern) (selected : d86471 q = 0) : d87649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86471, d87649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86471, d87649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86472 q = 0) : d87654 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86472, d87654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86472, d87654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro450 q selected
  have h4 (q : Pattern) (selected : d86473 q = 0) : d87655 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86473, d87655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86473, d87655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86474 q = 0) : d87656 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86474, d87656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86474, d87656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86478 q = 0) : d87664 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86478, d87664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86478, d87664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133483 q = 0) : d134644 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133483, d134644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133483, d134644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133484 q = 0) : d134645 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133484, d134645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133484, d134645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11376 (p : Pattern) (selected : d133488 p = 0) : d134653 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86472 q = 0) : d87654 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86472, d87654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86472, d87654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro450 q selected
  have h2 (q : Pattern) (selected : d86473 q = 0) : d87655 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86473, d87655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86473, d87655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86478 q = 0) : d87664 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86478, d87664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86478, d87664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133487 q = 0) : d134652 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133487, d134652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133487, d134652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133488 q = 0) : d134653 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133488, d134653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133488, d134653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11377 (p : Pattern) (selected : d133494 p = 0) : d134659 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133485 q = 0) : d134646 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133485, d134646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11375 q selected
    | true =>
      simp only [d133485, d134646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133486 q = 0) : d134647 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133486, d134647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133486, d134647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133489 q = 0) : d134654 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133489, d134654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11376 q selected
    | true =>
      simp only [d133489, d134654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133490 q = 0) : d134655 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133490, d134655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133490, d134655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133491 q = 0) : d134656 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133491, d134656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133491, d134656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133492 q = 0) : d134657 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133492, d134657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133492, d134657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133493 q = 0) : d134658 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133493, d134658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133493, d134658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133494 q = 0) : d134659 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133494, d134659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133494, d134659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11378 (p : Pattern) (selected : d133498 p = 0) : d134664 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133489 q = 0) : d134654 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133489, d134654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11376 q selected
    | true =>
      simp only [d133489, d134654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133490 q = 0) : d134655 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133490, d134655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133490, d134655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133495 q = 0) : d134661 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133495, d134661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133495, d134661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133496 q = 0) : d134662 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133496, d134662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133496, d134662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133497 q = 0) : d134663 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133497, d134663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133497, d134663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133498 q = 0) : d134664 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133498, d134664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133498, d134664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11379 (p : Pattern) (selected : d133505 p = 0) : d134671 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86445 q = 0) : d87648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86445, d87648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86445, d87648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro441 q selected
  have h2 (q : Pattern) (selected : d86446 q = 0) : d87649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86446, d87649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86446, d87649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86451 q = 0) : d87654 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86451, d87654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86451, d87654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro442 q selected
  have h4 (q : Pattern) (selected : d86452 q = 0) : d87655 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86452, d87655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86452, d87655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86453 q = 0) : d87656 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86453, d87656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86453, d87656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133501 q = 0) : d134667 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d133501, d134667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133501, d134667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3380 q selected
  have h7 (q : Pattern) (selected : d133502 q = 0) : d134668 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d133502, d134668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133502, d134668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133503 q = 0) : d134669 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d133503, d134669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133503, d134669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d133504 q = 0) : d134670 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133504, d134670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133504, d134670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133505 q = 0) : d134671 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133505, d134671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133505, d134671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11380 (p : Pattern) (selected : d133511 p = 0) : d134677 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133506 q = 0) : d134672 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133506, d134672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11379 q selected
    | true =>
      simp only [d133506, d134672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133507 q = 0) : d134673 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133507, d134673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133507, d134673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133508 q = 0) : d134674 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133508, d134674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133508, d134674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133509 q = 0) : d134675 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133509, d134675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133509, d134675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133510 q = 0) : d134676 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133510, d134676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133510, d134676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133511 q = 0) : d134677 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133511, d134677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133511, d134677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11381 (p : Pattern) (selected : d133517 p = 0) : d134683 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133482 q = 0) : d134660 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133482, d134660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11372 q selected
    | true =>
      simp only [d133482, d134660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11374 q selected
  have h2 (q : Pattern) (selected : d133499 q = 0) : d134665 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133499, d134665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11377 q selected
    | true =>
      simp only [d133499, d134665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11378 q selected
  have h3 (q : Pattern) (selected : d133500 q = 0) : d134666 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133500, d134666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133500, d134666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133512 q = 0) : d134678 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133512, d134678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11380 q selected
    | true =>
      simp only [d133512, d134678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133513 q = 0) : d134679 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133513, d134679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133513, d134679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133514 q = 0) : d134680 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133514, d134680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133514, d134680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133515 q = 0) : d134681 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133515, d134681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133515, d134681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133516 q = 0) : d134682 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133516, d134682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133516, d134682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133517 q = 0) : d134683 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133517, d134683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133517, d134683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11382 (p : Pattern) (selected : d133522 p = 0) : d134664 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133476 q = 0) : d134654 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133476, d134654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11373 q selected
    | true =>
      simp only [d133476, d134654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133477 q = 0) : d134655 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133477, d134655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133477, d134655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133519 q = 0) : d134661 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133519, d134661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133519, d134661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133520 q = 0) : d134662 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133520, d134662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133520, d134662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133521 q = 0) : d134663 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133521, d134663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133521, d134663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133522 q = 0) : d134664 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133522, d134664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133522, d134664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11383 (p : Pattern) (selected : d133528 p = 0) : d134690 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133523 q = 0) : d134685 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133523, d134685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11382 q selected
    | true =>
      simp only [d133523, d134685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133524 q = 0) : d134686 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133524, d134686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133524, d134686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133525 q = 0) : d134687 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133525, d134687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133525, d134687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133526 q = 0) : d134688 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133526, d134688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133526, d134688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133527 q = 0) : d134689 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133527, d134689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133527, d134689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133528 q = 0) : d134690 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133528, d134690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133528, d134690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11384 (p : Pattern) (selected : d133534 p = 0) : d134696 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133337 q = 0) : d134535 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133337, d134535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133337, d134535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11340 q selected
  have h2 (q : Pattern) (selected : d133338 q = 0) : d134536 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133338, d134536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133338, d134536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d133347 q = 0) : d134545 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133347, d134545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11340 q selected
    | true =>
      simp only [d133347, d134545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11343 q selected
  have h4 (q : Pattern) (selected : d133348 q = 0) : d134546 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133348, d134546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133348, d134546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133349 q = 0) : d134547 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133349, d134547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133349, d134547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133435 q = 0) : d134613 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133435, d134613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11356 q selected
    | true =>
      simp only [d133435, d134613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11365 q selected
  have h7 (q : Pattern) (selected : d133448 q = 0) : d134626 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133448, d134626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11366 q selected
    | true =>
      simp only [d133448, d134626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11367 q selected
  have h8 (q : Pattern) (selected : d133449 q = 0) : d134627 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133449, d134627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133449, d134627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133450 q = 0) : d134628 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133450, d134628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d133450, d134628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d133451 q = 0) : d134629 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133451, d134629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133451, d134629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133455 q = 0) : d134633 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133455, d134633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133455, d134633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11368 q selected
  have h12 (q : Pattern) (selected : d133457 q = 0) : d134635 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133457, d134635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133457, d134635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11369 q selected
  have h13 (q : Pattern) (selected : d133458 q = 0) : d134636 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133458, d134636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d133458, d134636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d133459 q = 0) : d134637 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133459, d134637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d133459, d134637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d133460 q = 0) : d134638 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133460, d134638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d133460, d134638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d133461 q = 0) : d134639 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d133461, d134639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133461, d134639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d133518 q = 0) : d134684 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133518, d134684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133518, d134684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11381 q selected
  have h18 (q : Pattern) (selected : d133529 q = 0) : d134691 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133529, d134691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133529, d134691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11383 q selected
  have h19 (q : Pattern) (selected : d133530 q = 0) : d134692 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133530, d134692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d133530, d134692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d133531 q = 0) : d134693 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133531, d134693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d133531, d134693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d133532 q = 0) : d134694 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133532, d134694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d133532, d134694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d133533 q = 0) : d134695 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d133533, d134695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d133533, d134695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d133534 q = 0) : d134696 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d133534, d134696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d133534, d134696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro11385 (p : Pattern) (selected : d133540 p = 0) : d134702 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133535 q = 0) : d134697 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d133535, d134697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133535, d134697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11384 q selected
  have h2 (q : Pattern) (selected : d133536 q = 0) : d134698 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d133536, d134698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133536, d134698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133537 q = 0) : d134699 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d133537, d134699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133537, d134699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133538 q = 0) : d134700 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d133538, d134700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133538, d134700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133539 q = 0) : d134701 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d133539, d134701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133539, d134701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133540 q = 0) : d134702 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d133540, d134702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133540, d134702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11386 (p : Pattern) (selected : d133545 p = 0) : d134707 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86528 q = 0) : d87711 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86528, d87711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86528, d87711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro472 q selected
  have h2 (q : Pattern) (selected : d86529 q = 0) : d87712 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86529, d87712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86529, d87712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86530 q = 0) : d87713 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86530, d87713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86530, d87713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro474 q selected
  have h4 (q : Pattern) (selected : d86531 q = 0) : d87714 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86531, d87714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86531, d87714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86532 q = 0) : d87715 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86532, d87715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86532, d87715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86536 q = 0) : d87719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86536, d87719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86536, d87719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133544 q = 0) : d134706 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133544, d134706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133544, d134706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133545 q = 0) : d134707 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133545, d134707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133545, d134707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11387 (p : Pattern) (selected : d133549 p = 0) : d134711 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86530 q = 0) : d87713 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86530, d87713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86530, d87713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro474 q selected
  have h2 (q : Pattern) (selected : d86531 q = 0) : d87714 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86531, d87714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86531, d87714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86536 q = 0) : d87719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86536, d87719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86536, d87719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133548 q = 0) : d134710 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133548, d134710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133548, d134710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133549 q = 0) : d134711 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133549, d134711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133549, d134711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11388 (p : Pattern) (selected : d133555 p = 0) : d134717 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133546 q = 0) : d134708 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133546, d134708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11386 q selected
    | true =>
      simp only [d133546, d134708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133547 q = 0) : d134709 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133547, d134709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133547, d134709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133550 q = 0) : d134712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11387 q selected
    | true =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133551 q = 0) : d134713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133552 q = 0) : d134714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133552, d134714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133552, d134714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133553 q = 0) : d134715 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133553, d134715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133553, d134715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133554 q = 0) : d134716 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133554, d134716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133554, d134716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133555 q = 0) : d134717 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133555, d134717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133555, d134717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11389 (p : Pattern) (selected : d133559 p = 0) : d134721 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133550 q = 0) : d134712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11387 q selected
    | true =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133551 q = 0) : d134713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133556 q = 0) : d134718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133556, d134718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133556, d134718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133557 q = 0) : d134719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133557, d134719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133557, d134719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133558 q = 0) : d134720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133558, d134720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133558, d134720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133559 q = 0) : d134721 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133559, d134721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133559, d134721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11390 (p : Pattern) (selected : d133565 p = 0) : d134727 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133560 q = 0) : d134722 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133560, d134722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11388 q selected
    | true =>
      simp only [d133560, d134722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11389 q selected
  have h2 (q : Pattern) (selected : d133561 q = 0) : d134723 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133561, d134723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133561, d134723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133562 q = 0) : d134724 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133562, d134724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133562, d134724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133563 q = 0) : d134725 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133563, d134725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133563, d134725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133564 q = 0) : d134726 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133564, d134726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133564, d134726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133565 q = 0) : d134727 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133565, d134727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133565, d134727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11391 (p : Pattern) (selected : d133568 p = 0) : d134730 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133546 q = 0) : d134708 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133546, d134708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11386 q selected
    | true =>
      simp only [d133546, d134708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133547 q = 0) : d134709 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133547, d134709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133547, d134709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133550 q = 0) : d134712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11387 q selected
    | true =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133551 q = 0) : d134713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133552 q = 0) : d134714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133552, d134714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133552, d134714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133553 q = 0) : d134715 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133553, d134715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133553, d134715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133554 q = 0) : d134716 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133554, d134716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133554, d134716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133568 q = 0) : d134730 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133568, d134730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133568, d134730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11392 (p : Pattern) (selected : d133569 p = 0) : d134731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133550 q = 0) : d134712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11387 q selected
    | true =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133551 q = 0) : d134713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133556 q = 0) : d134718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133556, d134718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133556, d134718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133557 q = 0) : d134719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133557, d134719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133557, d134719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133558 q = 0) : d134720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133558, d134720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133558, d134720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133569 q = 0) : d134731 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133569, d134731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133569, d134731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11393 (p : Pattern) (selected : d133575 p = 0) : d134737 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133560 q = 0) : d134722 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133560, d134722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11388 q selected
    | true =>
      simp only [d133560, d134722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11389 q selected
  have h2 (q : Pattern) (selected : d133561 q = 0) : d134723 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133561, d134723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133561, d134723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133562 q = 0) : d134724 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133562, d134724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133562, d134724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133563 q = 0) : d134725 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133563, d134725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133563, d134725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133564 q = 0) : d134726 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133564, d134726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133564, d134726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133570 q = 0) : d134732 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133570, d134732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11391 q selected
    | true =>
      simp only [d133570, d134732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11392 q selected
  have h7 (q : Pattern) (selected : d133571 q = 0) : d134733 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133571, d134733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133571, d134733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133572 q = 0) : d134734 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133572, d134734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133572, d134734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d133573 q = 0) : d134735 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133573, d134735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133573, d134735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133574 q = 0) : d134736 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133574, d134736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133574, d134736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133575 q = 0) : d134737 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133575, d134737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133575, d134737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11394 (p : Pattern) (selected : d133580 p = 0) : d134742 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133546 q = 0) : d134708 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133546, d134708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11386 q selected
    | true =>
      simp only [d133546, d134708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133547 q = 0) : d134709 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133547, d134709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133547, d134709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133550 q = 0) : d134712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11387 q selected
    | true =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133551 q = 0) : d134713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133552 q = 0) : d134714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133552, d134714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133552, d134714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133553 q = 0) : d134715 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133553, d134715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133553, d134715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133579 q = 0) : d134741 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133579, d134741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133579, d134741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133580 q = 0) : d134742 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133580, d134742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133580, d134742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11395 (p : Pattern) (selected : d133582 p = 0) : d134744 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133550 q = 0) : d134712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11387 q selected
    | true =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133551 q = 0) : d134713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133556 q = 0) : d134718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133556, d134718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133556, d134718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133557 q = 0) : d134719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133557, d134719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133557, d134719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133581 q = 0) : d134743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133581, d134743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133581, d134743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133582 q = 0) : d134744 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133582, d134744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133582, d134744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11396 (p : Pattern) (selected : d133589 p = 0) : d134751 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133546 q = 0) : d134708 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133546, d134708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11386 q selected
    | true =>
      simp only [d133546, d134708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133547 q = 0) : d134709 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133547, d134709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133547, d134709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133550 q = 0) : d134712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11387 q selected
    | true =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133551 q = 0) : d134713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133552 q = 0) : d134714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133552, d134714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133552, d134714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133587 q = 0) : d134749 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133587, d134749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133587, d134749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133588 q = 0) : d134750 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133588, d134750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133588, d134750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133589 q = 0) : d134751 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133589, d134751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133589, d134751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11397 (p : Pattern) (selected : d133592 p = 0) : d134754 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133550 q = 0) : d134712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11387 q selected
    | true =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133551 q = 0) : d134713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133556 q = 0) : d134718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133556, d134718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133556, d134718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133590 q = 0) : d134752 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133590, d134752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133590, d134752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133591 q = 0) : d134753 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133591, d134753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133591, d134753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133592 q = 0) : d134754 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133592, d134754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133592, d134754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11398 (p : Pattern) (selected : d133597 p = 0) : d134759 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86584 q = 0) : d87767 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86584, d87767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86584, d87767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro471 q selected
  have h2 (q : Pattern) (selected : d86585 q = 0) : d87768 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86585, d87768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86585, d87768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86528 q = 0) : d87711 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86528, d87711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86528, d87711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro472 q selected
  have h4 (q : Pattern) (selected : d86529 q = 0) : d87712 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86529, d87712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86529, d87712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86586 q = 0) : d87769 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86586, d87769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86586, d87769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86530 q = 0) : d87713 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86530, d87713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86530, d87713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro474 q selected
  have h7 (q : Pattern) (selected : d86531 q = 0) : d87714 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86531, d87714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86531, d87714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86532 q = 0) : d87715 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86532, d87715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86532, d87715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133596 q = 0) : d134758 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133596, d134758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133596, d134758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133597 q = 0) : d134759 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133597, d134759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133597, d134759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11399 (p : Pattern) (selected : d133603 p = 0) : d134765 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133598 q = 0) : d134760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133598, d134760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11398 q selected
    | true =>
      simp only [d133598, d134760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133599 q = 0) : d134761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133599, d134761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133599, d134761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133546 q = 0) : d134708 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133546, d134708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11386 q selected
    | true =>
      simp only [d133546, d134708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133547 q = 0) : d134709 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133547, d134709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133547, d134709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133600 q = 0) : d134762 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133600, d134762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133600, d134762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133601 q = 0) : d134763 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133601, d134763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133601, d134763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133602 q = 0) : d134764 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133602, d134764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133602, d134764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133603 q = 0) : d134765 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133603, d134765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133603, d134765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11400 (p : Pattern) (selected : d133606 p = 0) : d134707 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86595 q = 0) : d87711 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86595, d87711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86595, d87711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro505 q selected
  have h2 (q : Pattern) (selected : d86596 q = 0) : d87712 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86596, d87712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86596, d87712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86597 q = 0) : d87713 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86597, d87713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86597, d87713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro507 q selected
  have h4 (q : Pattern) (selected : d86598 q = 0) : d87714 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86598, d87714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86598, d87714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86599 q = 0) : d87715 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86599, d87715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86599, d87715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86603 q = 0) : d87719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86603, d87719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86603, d87719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133605 q = 0) : d134706 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133605, d134706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133605, d134706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133606 q = 0) : d134707 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133606, d134707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133606, d134707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11401 (p : Pattern) (selected : d133610 p = 0) : d134711 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86597 q = 0) : d87713 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86597, d87713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86597, d87713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro507 q selected
  have h2 (q : Pattern) (selected : d86598 q = 0) : d87714 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86598, d87714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86598, d87714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86603 q = 0) : d87719 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86603, d87719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86603, d87719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133609 q = 0) : d134710 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133609, d134710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133609, d134710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133610 q = 0) : d134711 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133610, d134711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133610, d134711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11402 (p : Pattern) (selected : d133616 p = 0) : d134717 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133607 q = 0) : d134708 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133607, d134708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11400 q selected
    | true =>
      simp only [d133607, d134708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133608 q = 0) : d134709 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133608, d134709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133608, d134709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133611 q = 0) : d134712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133611, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11401 q selected
    | true =>
      simp only [d133611, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133612 q = 0) : d134713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133612, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133612, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133613 q = 0) : d134714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133613, d134714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133613, d134714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133614 q = 0) : d134715 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133614, d134715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133614, d134715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133615 q = 0) : d134716 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133615, d134716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133615, d134716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133616 q = 0) : d134717 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133616, d134717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133616, d134717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11403 (p : Pattern) (selected : d133620 p = 0) : d134721 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133611 q = 0) : d134712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133611, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11401 q selected
    | true =>
      simp only [d133611, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133612 q = 0) : d134713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133612, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133612, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133617 q = 0) : d134718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133617, d134718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133617, d134718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133618 q = 0) : d134719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133618, d134719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133618, d134719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133619 q = 0) : d134720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133619, d134720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133619, d134720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133620 q = 0) : d134721 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133620, d134721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133620, d134721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11404 (p : Pattern) (selected : d133627 p = 0) : d134772 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86528 q = 0) : d87711 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86528, d87711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86528, d87711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro472 q selected
  have h2 (q : Pattern) (selected : d86529 q = 0) : d87712 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86529, d87712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86529, d87712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86530 q = 0) : d87713 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86530, d87713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86530, d87713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro474 q selected
  have h4 (q : Pattern) (selected : d86531 q = 0) : d87714 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86531, d87714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86531, d87714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86532 q = 0) : d87715 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86532, d87715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86532, d87715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133623 q = 0) : d134768 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d133623, d134768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133623, d134768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3388 q selected
  have h7 (q : Pattern) (selected : d133624 q = 0) : d134769 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d133624, d134769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133624, d134769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133625 q = 0) : d134770 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d133625, d134770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133625, d134770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d133626 q = 0) : d134771 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133626, d134771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133626, d134771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133627 q = 0) : d134772 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133627, d134772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133627, d134772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11405 (p : Pattern) (selected : d133633 p = 0) : d134778 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133628 q = 0) : d134773 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133628, d134773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11404 q selected
    | true =>
      simp only [d133628, d134773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133629 q = 0) : d134774 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133629, d134774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133629, d134774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133630 q = 0) : d134775 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133630, d134775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133630, d134775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133631 q = 0) : d134776 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133631, d134776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133631, d134776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133632 q = 0) : d134777 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133632, d134777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133632, d134777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133633 q = 0) : d134778 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133633, d134778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133633, d134778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11406 (p : Pattern) (selected : d133639 p = 0) : d134784 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133583 q = 0) : d134745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133583, d134745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11394 q selected
    | true =>
      simp only [d133583, d134745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11395 q selected
  have h2 (q : Pattern) (selected : d133584 q = 0) : d134746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133584, d134746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133584, d134746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133585 q = 0) : d134747 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133585, d134747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133585, d134747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133586 q = 0) : d134748 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133586, d134748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133586, d134748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133593 q = 0) : d134755 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133593, d134755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11396 q selected
    | true =>
      simp only [d133593, d134755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11397 q selected
  have h6 (q : Pattern) (selected : d133594 q = 0) : d134756 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133594, d134756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133594, d134756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133595 q = 0) : d134757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133595, d134757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133595, d134757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133604 q = 0) : d134766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133604, d134766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11399 q selected
    | true =>
      simp only [d133604, d134766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11388 q selected
  have h9 (q : Pattern) (selected : d133621 q = 0) : d134722 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133621, d134722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11402 q selected
    | true =>
      simp only [d133621, d134722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11403 q selected
  have h10 (q : Pattern) (selected : d133622 q = 0) : d134767 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133622, d134767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d133622, d134767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133634 q = 0) : d134779 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133634, d134779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11405 q selected
    | true =>
      simp only [d133634, d134779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d133635 q = 0) : d134780 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133635, d134780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d133635, d134780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d133636 q = 0) : d134781 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133636, d134781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133636, d134781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d133637 q = 0) : d134782 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133637, d134782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133637, d134782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d133638 q = 0) : d134783 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133638, d134783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133638, d134783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d133639 q = 0) : d134784 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133639, d134784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133639, d134784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro11407 (p : Pattern) (selected : d133640 p = 0) : d134785 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133546 q = 0) : d134708 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133546, d134708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11386 q selected
    | true =>
      simp only [d133546, d134708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133547 q = 0) : d134709 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133547, d134709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133547, d134709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133550 q = 0) : d134712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11387 q selected
    | true =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133551 q = 0) : d134713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133552 q = 0) : d134714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133552, d134714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133552, d134714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133553 q = 0) : d134715 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133553, d134715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133553, d134715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133579 q = 0) : d134741 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133579, d134741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133579, d134741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133640 q = 0) : d134785 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133640, d134785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133640, d134785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11408 (p : Pattern) (selected : d133641 p = 0) : d134786 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133550 q = 0) : d134712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11387 q selected
    | true =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133551 q = 0) : d134713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133556 q = 0) : d134718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133556, d134718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133556, d134718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133557 q = 0) : d134719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133557, d134719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133557, d134719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133581 q = 0) : d134743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133581, d134743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133581, d134743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133641 q = 0) : d134786 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133641, d134786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133641, d134786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11409 (p : Pattern) (selected : d133646 p = 0) : d134791 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133546 q = 0) : d134708 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133546, d134708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11386 q selected
    | true =>
      simp only [d133546, d134708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133547 q = 0) : d134709 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133547, d134709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133547, d134709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133550 q = 0) : d134712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11387 q selected
    | true =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133551 q = 0) : d134713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133552 q = 0) : d134714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133552, d134714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133552, d134714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133587 q = 0) : d134749 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133587, d134749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133587, d134749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133588 q = 0) : d134750 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133588, d134750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133588, d134750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133646 q = 0) : d134791 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133646, d134791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133646, d134791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11410 (p : Pattern) (selected : d133647 p = 0) : d134792 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133550 q = 0) : d134712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11387 q selected
    | true =>
      simp only [d133550, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133551 q = 0) : d134713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133551, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133556 q = 0) : d134718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133556, d134718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133556, d134718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133590 q = 0) : d134752 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133590, d134752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133590, d134752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133591 q = 0) : d134753 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133591, d134753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133591, d134753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133647 q = 0) : d134792 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133647, d134792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133647, d134792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11411 (p : Pattern) (selected : d133651 p = 0) : d134796 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133598 q = 0) : d134760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133598, d134760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11398 q selected
    | true =>
      simp only [d133598, d134760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133599 q = 0) : d134761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133599, d134761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133599, d134761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133546 q = 0) : d134708 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133546, d134708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11386 q selected
    | true =>
      simp only [d133546, d134708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133547 q = 0) : d134709 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133547, d134709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133547, d134709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133600 q = 0) : d134762 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133600, d134762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133600, d134762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133601 q = 0) : d134763 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133601, d134763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133601, d134763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133602 q = 0) : d134764 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133602, d134764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133602, d134764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133651 q = 0) : d134796 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133651, d134796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133651, d134796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11412 (p : Pattern) (selected : d133653 p = 0) : d134730 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133607 q = 0) : d134708 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133607, d134708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11400 q selected
    | true =>
      simp only [d133607, d134708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133608 q = 0) : d134709 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133608, d134709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133608, d134709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133611 q = 0) : d134712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133611, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11401 q selected
    | true =>
      simp only [d133611, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133612 q = 0) : d134713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133612, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133612, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133613 q = 0) : d134714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133613, d134714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133613, d134714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133614 q = 0) : d134715 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133614, d134715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133614, d134715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133615 q = 0) : d134716 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133615, d134716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133615, d134716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133653 q = 0) : d134730 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133653, d134730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133653, d134730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11413 (p : Pattern) (selected : d133654 p = 0) : d134731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133611 q = 0) : d134712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133611, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11401 q selected
    | true =>
      simp only [d133611, d134712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133612 q = 0) : d134713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133612, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133612, d134713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133617 q = 0) : d134718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133617, d134718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133617, d134718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133618 q = 0) : d134719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133618, d134719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133618, d134719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133619 q = 0) : d134720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133619, d134720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133619, d134720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133654 q = 0) : d134731 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133654, d134731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133654, d134731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11414 (p : Pattern) (selected : d133657 p = 0) : d134799 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133628 q = 0) : d134773 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133628, d134773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11404 q selected
    | true =>
      simp only [d133628, d134773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133629 q = 0) : d134774 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133629, d134774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133629, d134774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133630 q = 0) : d134775 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133630, d134775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133630, d134775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133631 q = 0) : d134776 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133631, d134776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133631, d134776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133632 q = 0) : d134777 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133632, d134777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133632, d134777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133657 q = 0) : d134799 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133657, d134799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133657, d134799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11415 (p : Pattern) (selected : d133663 p = 0) : d134805 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133583 q = 0) : d134745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133583, d134745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11394 q selected
    | true =>
      simp only [d133583, d134745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11395 q selected
  have h2 (q : Pattern) (selected : d133584 q = 0) : d134746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133584, d134746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133584, d134746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133585 q = 0) : d134747 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133585, d134747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133585, d134747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133586 q = 0) : d134748 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133586, d134748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133586, d134748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133593 q = 0) : d134755 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133593, d134755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11396 q selected
    | true =>
      simp only [d133593, d134755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11397 q selected
  have h6 (q : Pattern) (selected : d133594 q = 0) : d134756 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133594, d134756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133594, d134756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133595 q = 0) : d134757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133595, d134757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133595, d134757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133604 q = 0) : d134766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133604, d134766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11399 q selected
    | true =>
      simp only [d133604, d134766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11388 q selected
  have h9 (q : Pattern) (selected : d133621 q = 0) : d134722 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133621, d134722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11402 q selected
    | true =>
      simp only [d133621, d134722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11403 q selected
  have h10 (q : Pattern) (selected : d133622 q = 0) : d134767 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133622, d134767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d133622, d134767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133634 q = 0) : d134779 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133634, d134779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11405 q selected
    | true =>
      simp only [d133634, d134779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d133635 q = 0) : d134780 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133635, d134780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d133635, d134780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d133636 q = 0) : d134781 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133636, d134781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133636, d134781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d133637 q = 0) : d134782 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133637, d134782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133637, d134782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d133638 q = 0) : d134783 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133638, d134783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133638, d134783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d133642 q = 0) : d134787 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133642, d134787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11407 q selected
    | true =>
      simp only [d133642, d134787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11408 q selected
  have h17 (q : Pattern) (selected : d133643 q = 0) : d134788 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133643, d134788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133643, d134788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d133644 q = 0) : d134789 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133644, d134789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d133644, d134789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d133645 q = 0) : d134790 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133645, d134790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133645, d134790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d133648 q = 0) : d134793 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133648, d134793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11409 q selected
    | true =>
      simp only [d133648, d134793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11410 q selected
  have h21 (q : Pattern) (selected : d133649 q = 0) : d134794 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133649, d134794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133649, d134794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d133650 q = 0) : d134795 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133650, d134795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d133650, d134795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d133652 q = 0) : d134797 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133652, d134797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11411 q selected
    | true =>
      simp only [d133652, d134797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11391 q selected
  have h24 (q : Pattern) (selected : d133655 q = 0) : d134732 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133655, d134732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11412 q selected
    | true =>
      simp only [d133655, d134732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11413 q selected
  have h25 (q : Pattern) (selected : d133656 q = 0) : d134798 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133656, d134798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d133656, d134798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d133658 q = 0) : d134800 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133658, d134800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11414 q selected
    | true =>
      simp only [d133658, d134800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d133659 q = 0) : d134801 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133659, d134801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d133659, d134801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d133660 q = 0) : d134802 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133660, d134802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d133660, d134802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d133661 q = 0) : d134803 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133661, d134803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d133661, d134803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d133662 q = 0) : d134804 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133662, d134804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d133662, d134804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d133663 q = 0) : d134805 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133663, d134805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d133663, d134805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro11416 (p : Pattern) (selected : d133670 p = 0) : d134812 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133560 q = 0) : d134722 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133560, d134722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11388 q selected
    | true =>
      simp only [d133560, d134722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11389 q selected
  have h2 (q : Pattern) (selected : d133561 q = 0) : d134723 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133561, d134723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133561, d134723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133562 q = 0) : d134724 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133562, d134724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133562, d134724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133563 q = 0) : d134725 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133563, d134725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133563, d134725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133564 q = 0) : d134726 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133564, d134726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133564, d134726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133665 q = 0) : d134807 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133665, d134807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11389 q selected
    | true =>
      simp only [d133665, d134807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133666 q = 0) : d134808 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133666, d134808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133666, d134808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133667 q = 0) : d134809 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133667, d134809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133667, d134809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d133668 q = 0) : d134810 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133668, d134810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133668, d134810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133669 q = 0) : d134811 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133669, d134811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133669, d134811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133670 q = 0) : d134812 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133670, d134812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133670, d134812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11417 (p : Pattern) (selected : d133676 p = 0) : d134818 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133665 q = 0) : d134807 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133665, d134807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11389 q selected
    | true =>
      simp only [d133665, d134807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133666 q = 0) : d134808 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133666, d134808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133666, d134808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133667 q = 0) : d134809 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133667, d134809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133667, d134809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133668 q = 0) : d134810 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133668, d134810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133668, d134810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133669 q = 0) : d134811 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133669, d134811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133669, d134811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133671 q = 0) : d134813 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133671, d134813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11392 q selected
    | true =>
      simp only [d133671, d134813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133672 q = 0) : d134814 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133672, d134814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133672, d134814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133673 q = 0) : d134815 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133673, d134815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133673, d134815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d133674 q = 0) : d134816 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133674, d134816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133674, d134816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133675 q = 0) : d134817 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133675, d134817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133675, d134817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133676 q = 0) : d134818 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133676, d134818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133676, d134818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11418 (p : Pattern) (selected : d133683 p = 0) : d134825 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133652 q = 0) : d134797 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133652, d134797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11411 q selected
    | true =>
      simp only [d133652, d134797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11391 q selected
  have h2 (q : Pattern) (selected : d133655 q = 0) : d134732 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133655, d134732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11412 q selected
    | true =>
      simp only [d133655, d134732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11413 q selected
  have h3 (q : Pattern) (selected : d133656 q = 0) : d134798 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133656, d134798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133656, d134798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133658 q = 0) : d134800 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133658, d134800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11414 q selected
    | true =>
      simp only [d133658, d134800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133659 q = 0) : d134801 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133659, d134801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133659, d134801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133660 q = 0) : d134802 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133660, d134802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133660, d134802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133681 q = 0) : d134823 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133681, d134823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133681, d134823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133682 q = 0) : d134824 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133682, d134824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133682, d134824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133683 q = 0) : d134825 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133683, d134825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133683, d134825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11419 (p : Pattern) (selected : d133685 p = 0) : d134827 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133671 q = 0) : d134813 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133671, d134813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11392 q selected
    | true =>
      simp only [d133671, d134813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133672 q = 0) : d134814 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133672, d134814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133672, d134814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133673 q = 0) : d134815 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133673, d134815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133673, d134815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133674 q = 0) : d134816 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133674, d134816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133674, d134816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133675 q = 0) : d134817 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133675, d134817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133675, d134817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133685 q = 0) : d134827 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133685, d134827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133685, d134827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11420 (p : Pattern) (selected : d133692 p = 0) : d134834 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86678 q = 0) : d87837 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86678, d87837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86678, d87837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro526 q selected
  have h2 (q : Pattern) (selected : d86679 q = 0) : d87838 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86679, d87838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86679, d87838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86680 q = 0) : d87839 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86680, d87839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86680, d87839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro527 q selected
  have h4 (q : Pattern) (selected : d86681 q = 0) : d87840 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86681, d87840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86681, d87840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86682 q = 0) : d87841 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86682, d87841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86682, d87841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86686 q = 0) : d87845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86686, d87845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86686, d87845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro528 q selected
  have h7 (q : Pattern) (selected : d86687 q = 0) : d87846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86687, d87846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86687, d87846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86688 q = 0) : d87847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86688, d87847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86688, d87847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133691 q = 0) : d134833 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133691, d134833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133691, d134833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133692 q = 0) : d134834 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133692, d134834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133692, d134834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11421 (p : Pattern) (selected : d133696 p = 0) : d134838 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86680 q = 0) : d87839 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86680, d87839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86680, d87839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro527 q selected
  have h2 (q : Pattern) (selected : d86681 q = 0) : d87840 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86681, d87840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86681, d87840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86686 q = 0) : d87845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86686, d87845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86686, d87845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro528 q selected
  have h4 (q : Pattern) (selected : d86687 q = 0) : d87846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86687, d87846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86687, d87846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86688 q = 0) : d87847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86688, d87847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86688, d87847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86696 q = 0) : d87855 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86696, d87855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86696, d87855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133695 q = 0) : d134837 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133695, d134837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133695, d134837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133696 q = 0) : d134838 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133696, d134838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133696, d134838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11422 (p : Pattern) (selected : d133702 p = 0) : d134844 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133693 q = 0) : d134835 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133693, d134835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11420 q selected
    | true =>
      simp only [d133693, d134835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133694 q = 0) : d134836 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133694, d134836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133694, d134836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133697 q = 0) : d134839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133697, d134839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11421 q selected
    | true =>
      simp only [d133697, d134839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133698 q = 0) : d134840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133698, d134840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133698, d134840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133699 q = 0) : d134841 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133699, d134841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133699, d134841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133700 q = 0) : d134842 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133700, d134842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133700, d134842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133701 q = 0) : d134843 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133701, d134843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133701, d134843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133702 q = 0) : d134844 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133702, d134844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133702, d134844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11423 (p : Pattern) (selected : d133704 p = 0) : d134846 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86686 q = 0) : d87845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86686, d87845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86686, d87845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro528 q selected
  have h2 (q : Pattern) (selected : d86687 q = 0) : d87846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86687, d87846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86687, d87846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86696 q = 0) : d87855 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86696, d87855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86696, d87855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133703 q = 0) : d134845 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133703, d134845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133703, d134845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133704 q = 0) : d134846 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133704, d134846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133704, d134846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11424 (p : Pattern) (selected : d133710 p = 0) : d134852 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133697 q = 0) : d134839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133697, d134839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11421 q selected
    | true =>
      simp only [d133697, d134839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133698 q = 0) : d134840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133698, d134840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133698, d134840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133705 q = 0) : d134847 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133705, d134847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11423 q selected
    | true =>
      simp only [d133705, d134847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133706 q = 0) : d134848 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133706, d134848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133706, d134848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133707 q = 0) : d134849 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133707, d134849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133707, d134849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133708 q = 0) : d134850 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133708, d134850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133708, d134850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133709 q = 0) : d134851 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133709, d134851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133709, d134851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133710 q = 0) : d134852 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133710, d134852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133710, d134852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11425 (p : Pattern) (selected : d133713 p = 0) : d134838 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86705 q = 0) : d87839 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86705, d87839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86705, d87839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro535 q selected
  have h2 (q : Pattern) (selected : d86706 q = 0) : d87840 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86706, d87840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86706, d87840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86707 q = 0) : d87845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86707, d87845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86707, d87845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro536 q selected
  have h4 (q : Pattern) (selected : d86708 q = 0) : d87846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86708, d87846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86708, d87846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86709 q = 0) : d87847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86709, d87847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86709, d87847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86713 q = 0) : d87855 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86713, d87855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86713, d87855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133712 q = 0) : d134837 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133712, d134837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133712, d134837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133713 q = 0) : d134838 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133713, d134838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133713, d134838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11426 (p : Pattern) (selected : d133717 p = 0) : d134846 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86707 q = 0) : d87845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86707, d87845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86707, d87845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro536 q selected
  have h2 (q : Pattern) (selected : d86708 q = 0) : d87846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86708, d87846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86708, d87846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86713 q = 0) : d87855 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86713, d87855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86713, d87855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133716 q = 0) : d134845 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133716, d134845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133716, d134845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133717 q = 0) : d134846 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133717, d134846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133717, d134846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11427 (p : Pattern) (selected : d133723 p = 0) : d134852 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133714 q = 0) : d134839 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133714, d134839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11425 q selected
    | true =>
      simp only [d133714, d134839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133715 q = 0) : d134840 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133715, d134840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133715, d134840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133718 q = 0) : d134847 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133718, d134847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11426 q selected
    | true =>
      simp only [d133718, d134847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133719 q = 0) : d134848 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133719, d134848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133719, d134848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133720 q = 0) : d134849 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133720, d134849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133720, d134849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133721 q = 0) : d134850 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133721, d134850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133721, d134850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133722 q = 0) : d134851 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133722, d134851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133722, d134851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133723 q = 0) : d134852 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133723, d134852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133723, d134852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11428 (p : Pattern) (selected : d133727 p = 0) : d134857 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133718 q = 0) : d134847 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133718, d134847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11426 q selected
    | true =>
      simp only [d133718, d134847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133719 q = 0) : d134848 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133719, d134848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133719, d134848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133724 q = 0) : d134854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133724, d134854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133724, d134854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133725 q = 0) : d134855 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133725, d134855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133725, d134855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133726 q = 0) : d134856 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133726, d134856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133726, d134856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133727 q = 0) : d134857 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133727, d134857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133727, d134857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11429 (p : Pattern) (selected : d133734 p = 0) : d134864 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86680 q = 0) : d87839 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86680, d87839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86680, d87839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro527 q selected
  have h2 (q : Pattern) (selected : d86681 q = 0) : d87840 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86681, d87840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86681, d87840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86686 q = 0) : d87845 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86686, d87845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86686, d87845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro528 q selected
  have h4 (q : Pattern) (selected : d86687 q = 0) : d87846 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86687, d87846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86687, d87846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86688 q = 0) : d87847 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86688, d87847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86688, d87847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133730 q = 0) : d134860 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d133730, d134860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133730, d134860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3396 q selected
  have h7 (q : Pattern) (selected : d133731 q = 0) : d134861 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d133731, d134861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133731, d134861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133732 q = 0) : d134862 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d133732, d134862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133732, d134862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d133733 q = 0) : d134863 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133733, d134863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133733, d134863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133734 q = 0) : d134864 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133734, d134864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133734, d134864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11430 (p : Pattern) (selected : d133740 p = 0) : d134870 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133735 q = 0) : d134865 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133735, d134865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11429 q selected
    | true =>
      simp only [d133735, d134865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133736 q = 0) : d134866 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133736, d134866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133736, d134866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133737 q = 0) : d134867 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133737, d134867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133737, d134867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133738 q = 0) : d134868 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133738, d134868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133738, d134868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133739 q = 0) : d134869 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133739, d134869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133739, d134869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133740 q = 0) : d134870 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133740, d134870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133740, d134870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11431 (p : Pattern) (selected : d133746 p = 0) : d134876 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133711 q = 0) : d134853 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133711, d134853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11422 q selected
    | true =>
      simp only [d133711, d134853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11424 q selected
  have h2 (q : Pattern) (selected : d133728 q = 0) : d134858 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133728, d134858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11427 q selected
    | true =>
      simp only [d133728, d134858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11428 q selected
  have h3 (q : Pattern) (selected : d133729 q = 0) : d134859 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133729, d134859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133729, d134859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133741 q = 0) : d134871 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133741, d134871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11430 q selected
    | true =>
      simp only [d133741, d134871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133742 q = 0) : d134872 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133742, d134872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133742, d134872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133743 q = 0) : d134873 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133743, d134873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133743, d134873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133744 q = 0) : d134874 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133744, d134874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133744, d134874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133745 q = 0) : d134875 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133745, d134875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133745, d134875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133746 q = 0) : d134876 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133746, d134876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133746, d134876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11432 (p : Pattern) (selected : d133751 p = 0) : d134857 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133705 q = 0) : d134847 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133705, d134847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11423 q selected
    | true =>
      simp only [d133705, d134847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133706 q = 0) : d134848 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133706, d134848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133706, d134848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133748 q = 0) : d134854 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133748, d134854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133748, d134854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133749 q = 0) : d134855 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133749, d134855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133749, d134855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133750 q = 0) : d134856 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133750, d134856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133750, d134856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133751 q = 0) : d134857 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133751, d134857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133751, d134857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11433 (p : Pattern) (selected : d133757 p = 0) : d134883 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133752 q = 0) : d134878 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133752, d134878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11432 q selected
    | true =>
      simp only [d133752, d134878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133753 q = 0) : d134879 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133753, d134879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133753, d134879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133754 q = 0) : d134880 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133754, d134880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133754, d134880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133755 q = 0) : d134881 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133755, d134881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133755, d134881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133756 q = 0) : d134882 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133756, d134882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133756, d134882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133757 q = 0) : d134883 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133757, d134883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133757, d134883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11434 (p : Pattern) (selected : d133763 p = 0) : d134889 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133566 q = 0) : d134728 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133566, d134728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133566, d134728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11390 q selected
  have h2 (q : Pattern) (selected : d133567 q = 0) : d134729 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133567, d134729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133567, d134729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d133576 q = 0) : d134738 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133576, d134738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11390 q selected
    | true =>
      simp only [d133576, d134738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11393 q selected
  have h4 (q : Pattern) (selected : d133577 q = 0) : d134739 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133577, d134739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133577, d134739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133578 q = 0) : d134740 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133578, d134740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133578, d134740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133664 q = 0) : d134806 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133664, d134806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11406 q selected
    | true =>
      simp only [d133664, d134806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11415 q selected
  have h7 (q : Pattern) (selected : d133677 q = 0) : d134819 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133677, d134819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11416 q selected
    | true =>
      simp only [d133677, d134819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11417 q selected
  have h8 (q : Pattern) (selected : d133678 q = 0) : d134820 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133678, d134820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133678, d134820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133679 q = 0) : d134821 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133679, d134821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d133679, d134821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d133680 q = 0) : d134822 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133680, d134822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133680, d134822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133684 q = 0) : d134826 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133684, d134826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133684, d134826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11418 q selected
  have h12 (q : Pattern) (selected : d133686 q = 0) : d134828 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133686, d134828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133686, d134828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11419 q selected
  have h13 (q : Pattern) (selected : d133687 q = 0) : d134829 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133687, d134829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d133687, d134829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d133688 q = 0) : d134830 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133688, d134830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d133688, d134830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d133689 q = 0) : d134831 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133689, d134831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d133689, d134831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d133690 q = 0) : d134832 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d133690, d134832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133690, d134832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d133747 q = 0) : d134877 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133747, d134877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133747, d134877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11431 q selected
  have h18 (q : Pattern) (selected : d133758 q = 0) : d134884 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133758, d134884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133758, d134884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11433 q selected
  have h19 (q : Pattern) (selected : d133759 q = 0) : d134885 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133759, d134885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d133759, d134885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d133760 q = 0) : d134886 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133760, d134886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d133760, d134886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d133761 q = 0) : d134887 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133761, d134887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d133761, d134887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d133762 q = 0) : d134888 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d133762, d134888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d133762, d134888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d133763 q = 0) : d134889 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d133763, d134889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d133763, d134889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro11435 (p : Pattern) (selected : d133769 p = 0) : d134895 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133764 q = 0) : d134890 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d133764, d134890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133764, d134890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11434 q selected
  have h2 (q : Pattern) (selected : d133765 q = 0) : d134891 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d133765, d134891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133765, d134891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133766 q = 0) : d134892 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d133766, d134892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133766, d134892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133767 q = 0) : d134893 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d133767, d134893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133767, d134893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133768 q = 0) : d134894 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d133768, d134894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133768, d134894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133769 q = 0) : d134895 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d133769, d134895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133769, d134895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11436 (p : Pattern) (selected : d133775 p = 0) : d134901 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86764 q = 0) : d87903 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86764, d87903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86764, d87903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro561 q selected
  have h2 (q : Pattern) (selected : d86765 q = 0) : d87904 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86765, d87904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86765, d87904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86766 q = 0) : d87905 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86766, d87905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86766, d87905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro563 q selected
  have h4 (q : Pattern) (selected : d86767 q = 0) : d87906 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86767, d87906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86767, d87906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86768 q = 0) : d87907 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86768, d87907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86768, d87907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86772 q = 0) : d87911 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86772, d87911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86772, d87911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133774 q = 0) : d134900 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133774, d134900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133774, d134900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133775 q = 0) : d134901 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133775, d134901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133775, d134901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11437 (p : Pattern) (selected : d133779 p = 0) : d134905 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86766 q = 0) : d87905 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86766, d87905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86766, d87905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro563 q selected
  have h2 (q : Pattern) (selected : d86767 q = 0) : d87906 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86767, d87906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86767, d87906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86772 q = 0) : d87911 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86772, d87911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86772, d87911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133778 q = 0) : d134904 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133778, d134904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133778, d134904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133779 q = 0) : d134905 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133779, d134905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133779, d134905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11438 (p : Pattern) (selected : d133785 p = 0) : d134911 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133776 q = 0) : d134902 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133776, d134902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11436 q selected
    | true =>
      simp only [d133776, d134902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133777 q = 0) : d134903 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133777, d134903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133777, d134903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133780 q = 0) : d134906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11437 q selected
    | true =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133781 q = 0) : d134907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133782 q = 0) : d134908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133782, d134908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133782, d134908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133783 q = 0) : d134909 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133783, d134909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133783, d134909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133784 q = 0) : d134910 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133784, d134910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133784, d134910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133785 q = 0) : d134911 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133785, d134911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133785, d134911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11439 (p : Pattern) (selected : d133789 p = 0) : d134915 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133780 q = 0) : d134906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11437 q selected
    | true =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133781 q = 0) : d134907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133786 q = 0) : d134912 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133786, d134912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133786, d134912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133787 q = 0) : d134913 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133787, d134913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133787, d134913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133788 q = 0) : d134914 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133788, d134914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133788, d134914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133789 q = 0) : d134915 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133789, d134915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133789, d134915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11440 (p : Pattern) (selected : d133795 p = 0) : d134921 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133790 q = 0) : d134916 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133790, d134916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11438 q selected
    | true =>
      simp only [d133790, d134916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11439 q selected
  have h2 (q : Pattern) (selected : d133791 q = 0) : d134917 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133791, d134917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133791, d134917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133792 q = 0) : d134918 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133792, d134918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133792, d134918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133793 q = 0) : d134919 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133793, d134919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133793, d134919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133794 q = 0) : d134920 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133794, d134920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133794, d134920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133795 q = 0) : d134921 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133795, d134921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133795, d134921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11441 (p : Pattern) (selected : d133798 p = 0) : d134924 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133776 q = 0) : d134902 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133776, d134902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11436 q selected
    | true =>
      simp only [d133776, d134902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133777 q = 0) : d134903 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133777, d134903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133777, d134903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133780 q = 0) : d134906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11437 q selected
    | true =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133781 q = 0) : d134907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133782 q = 0) : d134908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133782, d134908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133782, d134908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133783 q = 0) : d134909 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133783, d134909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133783, d134909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133784 q = 0) : d134910 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133784, d134910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133784, d134910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133798 q = 0) : d134924 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133798, d134924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133798, d134924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11442 (p : Pattern) (selected : d133799 p = 0) : d134925 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133780 q = 0) : d134906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11437 q selected
    | true =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133781 q = 0) : d134907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133786 q = 0) : d134912 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133786, d134912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133786, d134912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133787 q = 0) : d134913 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133787, d134913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133787, d134913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133788 q = 0) : d134914 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133788, d134914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133788, d134914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133799 q = 0) : d134925 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133799, d134925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133799, d134925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11443 (p : Pattern) (selected : d133805 p = 0) : d134931 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133790 q = 0) : d134916 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133790, d134916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11438 q selected
    | true =>
      simp only [d133790, d134916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11439 q selected
  have h2 (q : Pattern) (selected : d133791 q = 0) : d134917 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133791, d134917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133791, d134917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133792 q = 0) : d134918 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133792, d134918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133792, d134918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133793 q = 0) : d134919 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133793, d134919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133793, d134919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133794 q = 0) : d134920 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133794, d134920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133794, d134920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133800 q = 0) : d134926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133800, d134926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11441 q selected
    | true =>
      simp only [d133800, d134926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11442 q selected
  have h7 (q : Pattern) (selected : d133801 q = 0) : d134927 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133801, d134927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133801, d134927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133802 q = 0) : d134928 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133802, d134928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133802, d134928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d133803 q = 0) : d134929 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133803, d134929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133803, d134929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133804 q = 0) : d134930 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133804, d134930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133804, d134930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133805 q = 0) : d134931 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133805, d134931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133805, d134931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11444 (p : Pattern) (selected : d133810 p = 0) : d134936 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133776 q = 0) : d134902 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133776, d134902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11436 q selected
    | true =>
      simp only [d133776, d134902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133777 q = 0) : d134903 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133777, d134903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133777, d134903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133780 q = 0) : d134906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11437 q selected
    | true =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133781 q = 0) : d134907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133782 q = 0) : d134908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133782, d134908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133782, d134908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133783 q = 0) : d134909 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133783, d134909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133783, d134909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133809 q = 0) : d134935 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133809, d134935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133809, d134935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133810 q = 0) : d134936 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133810, d134936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133810, d134936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11445 (p : Pattern) (selected : d133812 p = 0) : d134938 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133780 q = 0) : d134906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11437 q selected
    | true =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133781 q = 0) : d134907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133786 q = 0) : d134912 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133786, d134912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133786, d134912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133787 q = 0) : d134913 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133787, d134913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133787, d134913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133811 q = 0) : d134937 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133811, d134937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133811, d134937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133812 q = 0) : d134938 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133812, d134938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133812, d134938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11446 (p : Pattern) (selected : d133819 p = 0) : d134945 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133776 q = 0) : d134902 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133776, d134902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11436 q selected
    | true =>
      simp only [d133776, d134902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133777 q = 0) : d134903 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133777, d134903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133777, d134903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133780 q = 0) : d134906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11437 q selected
    | true =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133781 q = 0) : d134907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133782 q = 0) : d134908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133782, d134908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133782, d134908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133817 q = 0) : d134943 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133817, d134943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133817, d134943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133818 q = 0) : d134944 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133818, d134944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133818, d134944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133819 q = 0) : d134945 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133819, d134945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133819, d134945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11447 (p : Pattern) (selected : d133822 p = 0) : d134948 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133780 q = 0) : d134906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11437 q selected
    | true =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133781 q = 0) : d134907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133786 q = 0) : d134912 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133786, d134912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133786, d134912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133820 q = 0) : d134946 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133820, d134946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133820, d134946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133821 q = 0) : d134947 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133821, d134947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133821, d134947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133822 q = 0) : d134948 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133822, d134948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133822, d134948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11448 (p : Pattern) (selected : d133827 p = 0) : d134953 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86820 q = 0) : d87959 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86820, d87959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86820, d87959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro560 q selected
  have h2 (q : Pattern) (selected : d86821 q = 0) : d87960 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86821, d87960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86821, d87960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86764 q = 0) : d87903 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86764, d87903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86764, d87903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro561 q selected
  have h4 (q : Pattern) (selected : d86765 q = 0) : d87904 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86765, d87904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86765, d87904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86822 q = 0) : d87961 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86822, d87961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86822, d87961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86766 q = 0) : d87905 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86766, d87905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86766, d87905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro563 q selected
  have h7 (q : Pattern) (selected : d86767 q = 0) : d87906 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86767, d87906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86767, d87906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86768 q = 0) : d87907 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86768, d87907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86768, d87907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133826 q = 0) : d134952 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133826, d134952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133826, d134952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133827 q = 0) : d134953 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133827, d134953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133827, d134953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11449 (p : Pattern) (selected : d133833 p = 0) : d134959 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133828 q = 0) : d134954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133828, d134954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11448 q selected
    | true =>
      simp only [d133828, d134954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133829 q = 0) : d134955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133829, d134955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133829, d134955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133776 q = 0) : d134902 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133776, d134902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11436 q selected
    | true =>
      simp only [d133776, d134902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133777 q = 0) : d134903 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133777, d134903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133777, d134903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133830 q = 0) : d134956 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133830, d134956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133830, d134956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133831 q = 0) : d134957 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133831, d134957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133831, d134957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133832 q = 0) : d134958 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133832, d134958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133832, d134958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133833 q = 0) : d134959 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133833, d134959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133833, d134959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11450 (p : Pattern) (selected : d133836 p = 0) : d134901 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86831 q = 0) : d87903 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86831, d87903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86831, d87903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro595 q selected
  have h2 (q : Pattern) (selected : d86832 q = 0) : d87904 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86832, d87904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86832, d87904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86833 q = 0) : d87905 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86833, d87905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86833, d87905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro597 q selected
  have h4 (q : Pattern) (selected : d86834 q = 0) : d87906 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86834, d87906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86834, d87906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86835 q = 0) : d87907 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86835, d87907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86835, d87907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86839 q = 0) : d87911 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86839, d87911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86839, d87911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133835 q = 0) : d134900 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133835, d134900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133835, d134900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133836 q = 0) : d134901 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133836, d134901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133836, d134901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11451 (p : Pattern) (selected : d133840 p = 0) : d134905 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86833 q = 0) : d87905 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86833, d87905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86833, d87905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro597 q selected
  have h2 (q : Pattern) (selected : d86834 q = 0) : d87906 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86834, d87906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86834, d87906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86839 q = 0) : d87911 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86839, d87911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86839, d87911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133839 q = 0) : d134904 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133839, d134904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133839, d134904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133840 q = 0) : d134905 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133840, d134905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133840, d134905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11452 (p : Pattern) (selected : d133846 p = 0) : d134911 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133837 q = 0) : d134902 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133837, d134902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11450 q selected
    | true =>
      simp only [d133837, d134902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133838 q = 0) : d134903 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133838, d134903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133838, d134903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133841 q = 0) : d134906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133841, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11451 q selected
    | true =>
      simp only [d133841, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133842 q = 0) : d134907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133842, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133842, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133843 q = 0) : d134908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133843, d134908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133843, d134908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133844 q = 0) : d134909 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133844, d134909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133844, d134909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133845 q = 0) : d134910 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133845, d134910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133845, d134910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133846 q = 0) : d134911 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133846, d134911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133846, d134911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro11453 (p : Pattern) (selected : d133850 p = 0) : d134915 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133841 q = 0) : d134906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133841, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11451 q selected
    | true =>
      simp only [d133841, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133842 q = 0) : d134907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133842, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133842, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133847 q = 0) : d134912 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133847, d134912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133847, d134912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133848 q = 0) : d134913 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133848, d134913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133848, d134913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133849 q = 0) : d134914 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133849, d134914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133849, d134914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133850 q = 0) : d134915 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133850, d134915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133850, d134915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11454 (p : Pattern) (selected : d133857 p = 0) : d134966 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86764 q = 0) : d87903 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86764, d87903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86764, d87903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro561 q selected
  have h2 (q : Pattern) (selected : d86765 q = 0) : d87904 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86765, d87904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86765, d87904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86766 q = 0) : d87905 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86766, d87905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86766, d87905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro563 q selected
  have h4 (q : Pattern) (selected : d86767 q = 0) : d87906 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86767, d87906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86767, d87906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86768 q = 0) : d87907 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86768, d87907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86768, d87907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133853 q = 0) : d134962 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d133853, d134962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133853, d134962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3404 q selected
  have h7 (q : Pattern) (selected : d133854 q = 0) : d134963 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d133854, d134963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133854, d134963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133855 q = 0) : d134964 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d133855, d134964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133855, d134964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d133856 q = 0) : d134965 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133856, d134965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133856, d134965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133857 q = 0) : d134966 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133857, d134966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133857, d134966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11455 (p : Pattern) (selected : d133863 p = 0) : d134972 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133858 q = 0) : d134967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133858, d134967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11454 q selected
    | true =>
      simp only [d133858, d134967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133859 q = 0) : d134968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133859, d134968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133859, d134968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133860 q = 0) : d134969 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133860, d134969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133860, d134969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133861 q = 0) : d134970 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133861, d134970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133861, d134970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133862 q = 0) : d134971 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133862, d134971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133862, d134971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133863 q = 0) : d134972 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133863, d134972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133863, d134972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11456 (p : Pattern) (selected : d133869 p = 0) : d134978 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133813 q = 0) : d134939 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133813, d134939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11444 q selected
    | true =>
      simp only [d133813, d134939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11445 q selected
  have h2 (q : Pattern) (selected : d133814 q = 0) : d134940 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133814, d134940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133814, d134940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133815 q = 0) : d134941 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133815, d134941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133815, d134941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133816 q = 0) : d134942 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133816, d134942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133816, d134942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133823 q = 0) : d134949 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133823, d134949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11446 q selected
    | true =>
      simp only [d133823, d134949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11447 q selected
  have h6 (q : Pattern) (selected : d133824 q = 0) : d134950 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133824, d134950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133824, d134950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133825 q = 0) : d134951 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133825, d134951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133825, d134951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133834 q = 0) : d134960 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133834, d134960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11449 q selected
    | true =>
      simp only [d133834, d134960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11438 q selected
  have h9 (q : Pattern) (selected : d133851 q = 0) : d134916 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133851, d134916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11452 q selected
    | true =>
      simp only [d133851, d134916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11453 q selected
  have h10 (q : Pattern) (selected : d133852 q = 0) : d134961 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133852, d134961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d133852, d134961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133864 q = 0) : d134973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133864, d134973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11455 q selected
    | true =>
      simp only [d133864, d134973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d133865 q = 0) : d134974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133865, d134974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d133865, d134974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d133866 q = 0) : d134975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133866, d134975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133866, d134975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d133867 q = 0) : d134976 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133867, d134976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133867, d134976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d133868 q = 0) : d134977 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133868, d134977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133868, d134977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d133869 q = 0) : d134978 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133869, d134978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133869, d134978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro11457 (p : Pattern) (selected : d133870 p = 0) : d134979 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133776 q = 0) : d134902 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133776, d134902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11436 q selected
    | true =>
      simp only [d133776, d134902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133777 q = 0) : d134903 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133777, d134903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133777, d134903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133780 q = 0) : d134906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11437 q selected
    | true =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133781 q = 0) : d134907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133782 q = 0) : d134908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133782, d134908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133782, d134908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133783 q = 0) : d134909 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133783, d134909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133783, d134909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133809 q = 0) : d134935 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133809, d134935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133809, d134935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133870 q = 0) : d134979 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133870, d134979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133870, d134979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11458 (p : Pattern) (selected : d133871 p = 0) : d134980 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133780 q = 0) : d134906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11437 q selected
    | true =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133781 q = 0) : d134907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133786 q = 0) : d134912 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133786, d134912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133786, d134912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133787 q = 0) : d134913 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133787, d134913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133787, d134913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133811 q = 0) : d134937 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133811, d134937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133811, d134937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133871 q = 0) : d134980 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133871, d134980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133871, d134980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11459 (p : Pattern) (selected : d133876 p = 0) : d134985 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133776 q = 0) : d134902 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133776, d134902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11436 q selected
    | true =>
      simp only [d133776, d134902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133777 q = 0) : d134903 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133777, d134903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133777, d134903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133780 q = 0) : d134906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11437 q selected
    | true =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133781 q = 0) : d134907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133782 q = 0) : d134908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133782, d134908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133782, d134908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133817 q = 0) : d134943 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133817, d134943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133817, d134943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133818 q = 0) : d134944 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133818, d134944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133818, d134944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133876 q = 0) : d134985 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133876, d134985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133876, d134985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11460 (p : Pattern) (selected : d133877 p = 0) : d134986 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133780 q = 0) : d134906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11437 q selected
    | true =>
      simp only [d133780, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133781 q = 0) : d134907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133781, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133786 q = 0) : d134912 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133786, d134912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133786, d134912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133820 q = 0) : d134946 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133820, d134946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133820, d134946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133821 q = 0) : d134947 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133821, d134947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133821, d134947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133877 q = 0) : d134986 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133877, d134986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133877, d134986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11461 (p : Pattern) (selected : d133881 p = 0) : d134990 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133828 q = 0) : d134954 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133828, d134954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11448 q selected
    | true =>
      simp only [d133828, d134954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133829 q = 0) : d134955 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133829, d134955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133829, d134955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133776 q = 0) : d134902 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133776, d134902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11436 q selected
    | true =>
      simp only [d133776, d134902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133777 q = 0) : d134903 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133777, d134903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133777, d134903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133830 q = 0) : d134956 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133830, d134956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133830, d134956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133831 q = 0) : d134957 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133831, d134957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133831, d134957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133832 q = 0) : d134958 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133832, d134958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133832, d134958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133881 q = 0) : d134990 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133881, d134990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133881, d134990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11462 (p : Pattern) (selected : d133883 p = 0) : d134924 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133837 q = 0) : d134902 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133837, d134902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11450 q selected
    | true =>
      simp only [d133837, d134902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133838 q = 0) : d134903 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133838, d134903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133838, d134903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133841 q = 0) : d134906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133841, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11451 q selected
    | true =>
      simp only [d133841, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133842 q = 0) : d134907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133842, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133842, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133843 q = 0) : d134908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133843, d134908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133843, d134908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133844 q = 0) : d134909 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133844, d134909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133844, d134909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133845 q = 0) : d134910 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133845, d134910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133845, d134910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133883 q = 0) : d134924 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133883, d134924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133883, d134924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11463 (p : Pattern) (selected : d133884 p = 0) : d134925 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133841 q = 0) : d134906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133841, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11451 q selected
    | true =>
      simp only [d133841, d134906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133842 q = 0) : d134907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133842, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133842, d134907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133847 q = 0) : d134912 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133847, d134912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133847, d134912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133848 q = 0) : d134913 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133848, d134913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133848, d134913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133849 q = 0) : d134914 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133849, d134914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133849, d134914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133884 q = 0) : d134925 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133884, d134925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133884, d134925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11464 (p : Pattern) (selected : d133887 p = 0) : d134993 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133858 q = 0) : d134967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133858, d134967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11454 q selected
    | true =>
      simp only [d133858, d134967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133859 q = 0) : d134968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133859, d134968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133859, d134968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133860 q = 0) : d134969 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133860, d134969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133860, d134969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133861 q = 0) : d134970 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133861, d134970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133861, d134970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133862 q = 0) : d134971 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133862, d134971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133862, d134971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133887 q = 0) : d134993 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133887, d134993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133887, d134993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11465 (p : Pattern) (selected : d133893 p = 0) : d134999 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133813 q = 0) : d134939 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133813, d134939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11444 q selected
    | true =>
      simp only [d133813, d134939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11445 q selected
  have h2 (q : Pattern) (selected : d133814 q = 0) : d134940 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133814, d134940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133814, d134940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133815 q = 0) : d134941 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133815, d134941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133815, d134941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133816 q = 0) : d134942 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133816, d134942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133816, d134942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133823 q = 0) : d134949 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133823, d134949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11446 q selected
    | true =>
      simp only [d133823, d134949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11447 q selected
  have h6 (q : Pattern) (selected : d133824 q = 0) : d134950 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133824, d134950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133824, d134950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133825 q = 0) : d134951 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133825, d134951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133825, d134951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133834 q = 0) : d134960 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133834, d134960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11449 q selected
    | true =>
      simp only [d133834, d134960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11438 q selected
  have h9 (q : Pattern) (selected : d133851 q = 0) : d134916 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133851, d134916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11452 q selected
    | true =>
      simp only [d133851, d134916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11453 q selected
  have h10 (q : Pattern) (selected : d133852 q = 0) : d134961 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133852, d134961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d133852, d134961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133864 q = 0) : d134973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133864, d134973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11455 q selected
    | true =>
      simp only [d133864, d134973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d133865 q = 0) : d134974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133865, d134974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d133865, d134974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d133866 q = 0) : d134975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133866, d134975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133866, d134975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d133867 q = 0) : d134976 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133867, d134976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133867, d134976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d133868 q = 0) : d134977 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133868, d134977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133868, d134977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d133872 q = 0) : d134981 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133872, d134981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11457 q selected
    | true =>
      simp only [d133872, d134981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11458 q selected
  have h17 (q : Pattern) (selected : d133873 q = 0) : d134982 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133873, d134982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133873, d134982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d133874 q = 0) : d134983 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133874, d134983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d133874, d134983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d133875 q = 0) : d134984 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133875, d134984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133875, d134984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d133878 q = 0) : d134987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133878, d134987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11459 q selected
    | true =>
      simp only [d133878, d134987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11460 q selected
  have h21 (q : Pattern) (selected : d133879 q = 0) : d134988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133879, d134988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133879, d134988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d133880 q = 0) : d134989 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133880, d134989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d133880, d134989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d133882 q = 0) : d134991 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133882, d134991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11461 q selected
    | true =>
      simp only [d133882, d134991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11441 q selected
  have h24 (q : Pattern) (selected : d133885 q = 0) : d134926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133885, d134926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11462 q selected
    | true =>
      simp only [d133885, d134926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11463 q selected
  have h25 (q : Pattern) (selected : d133886 q = 0) : d134992 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133886, d134992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d133886, d134992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d133888 q = 0) : d134994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133888, d134994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11464 q selected
    | true =>
      simp only [d133888, d134994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d133889 q = 0) : d134995 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133889, d134995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d133889, d134995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d133890 q = 0) : d134996 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133890, d134996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d133890, d134996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d133891 q = 0) : d134997 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133891, d134997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d133891, d134997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d133892 q = 0) : d134998 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133892, d134998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d133892, d134998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d133893 q = 0) : d134999 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133893, d134999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d133893, d134999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro11466 (p : Pattern) (selected : d133900 p = 0) : d135006 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133790 q = 0) : d134916 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133790, d134916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11438 q selected
    | true =>
      simp only [d133790, d134916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11439 q selected
  have h2 (q : Pattern) (selected : d133791 q = 0) : d134917 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133791, d134917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133791, d134917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133792 q = 0) : d134918 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133792, d134918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133792, d134918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133793 q = 0) : d134919 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133793, d134919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133793, d134919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133794 q = 0) : d134920 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133794, d134920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133794, d134920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133895 q = 0) : d135001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133895, d135001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11439 q selected
    | true =>
      simp only [d133895, d135001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133896 q = 0) : d135002 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133896, d135002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133896, d135002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133897 q = 0) : d135003 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133897, d135003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133897, d135003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d133898 q = 0) : d135004 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133898, d135004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133898, d135004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133899 q = 0) : d135005 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133899, d135005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133899, d135005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133900 q = 0) : d135006 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133900, d135006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133900, d135006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11467 (p : Pattern) (selected : d133906 p = 0) : d135012 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133895 q = 0) : d135001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133895, d135001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11439 q selected
    | true =>
      simp only [d133895, d135001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133896 q = 0) : d135002 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133896, d135002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133896, d135002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133897 q = 0) : d135003 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133897, d135003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133897, d135003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133898 q = 0) : d135004 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133898, d135004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133898, d135004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133899 q = 0) : d135005 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133899, d135005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133899, d135005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133901 q = 0) : d135007 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133901, d135007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11442 q selected
    | true =>
      simp only [d133901, d135007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133902 q = 0) : d135008 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133902, d135008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133902, d135008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133903 q = 0) : d135009 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133903, d135009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133903, d135009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d133904 q = 0) : d135010 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133904, d135010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133904, d135010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133905 q = 0) : d135011 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133905, d135011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133905, d135011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133906 q = 0) : d135012 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133906, d135012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133906, d135012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro11468 (p : Pattern) (selected : d133913 p = 0) : d135019 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133882 q = 0) : d134991 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133882, d134991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11461 q selected
    | true =>
      simp only [d133882, d134991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11441 q selected
  have h2 (q : Pattern) (selected : d133885 q = 0) : d134926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133885, d134926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11462 q selected
    | true =>
      simp only [d133885, d134926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11463 q selected
  have h3 (q : Pattern) (selected : d133886 q = 0) : d134992 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133886, d134992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133886, d134992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133888 q = 0) : d134994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133888, d134994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11464 q selected
    | true =>
      simp only [d133888, d134994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133889 q = 0) : d134995 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133889, d134995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133889, d134995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133890 q = 0) : d134996 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133890, d134996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133890, d134996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133911 q = 0) : d135017 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133911, d135017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133911, d135017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133912 q = 0) : d135018 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133912, d135018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133912, d135018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133913 q = 0) : d135019 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133913, d135019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133913, d135019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11469 (p : Pattern) (selected : d133915 p = 0) : d135021 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133901 q = 0) : d135007 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133901, d135007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11442 q selected
    | true =>
      simp only [d133901, d135007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133902 q = 0) : d135008 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133902, d135008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133902, d135008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133903 q = 0) : d135009 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133903, d135009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133903, d135009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133904 q = 0) : d135010 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133904, d135010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133904, d135010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133905 q = 0) : d135011 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133905, d135011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133905, d135011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133915 q = 0) : d135021 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133915, d135021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133915, d135021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11470 (p : Pattern) (selected : d133922 p = 0) : d135028 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86914 q = 0) : d88029 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86914, d88029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86914, d88029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro616 q selected
  have h2 (q : Pattern) (selected : d86915 q = 0) : d88030 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86915, d88030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86915, d88030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86916 q = 0) : d88031 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86916, d88031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86916, d88031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro617 q selected
  have h4 (q : Pattern) (selected : d86917 q = 0) : d88032 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86917, d88032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86917, d88032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86918 q = 0) : d88033 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86918, d88033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86918, d88033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86922 q = 0) : d88037 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86922, d88037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86922, d88037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro618 q selected
  have h7 (q : Pattern) (selected : d86923 q = 0) : d88038 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86923, d88038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86923, d88038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d86924 q = 0) : d88039 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86924, d88039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86924, d88039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133921 q = 0) : d135027 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133921, d135027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133921, d135027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133922 q = 0) : d135028 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133922, d135028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133922, d135028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11471 (p : Pattern) (selected : d133926 p = 0) : d135032 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86916 q = 0) : d88031 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86916, d88031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86916, d88031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro617 q selected
  have h2 (q : Pattern) (selected : d86917 q = 0) : d88032 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86917, d88032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86917, d88032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86922 q = 0) : d88037 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86922, d88037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86922, d88037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro618 q selected
  have h4 (q : Pattern) (selected : d86923 q = 0) : d88038 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86923, d88038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86923, d88038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86924 q = 0) : d88039 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86924, d88039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86924, d88039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86932 q = 0) : d88047 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86932, d88047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86932, d88047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133925 q = 0) : d135031 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133925, d135031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133925, d135031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133926 q = 0) : d135032 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133926, d135032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133926, d135032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11472 (p : Pattern) (selected : d133932 p = 0) : d135038 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133923 q = 0) : d135029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133923, d135029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11470 q selected
    | true =>
      simp only [d133923, d135029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133924 q = 0) : d135030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133924, d135030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133924, d135030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133927 q = 0) : d135033 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133927, d135033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11471 q selected
    | true =>
      simp only [d133927, d135033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133928 q = 0) : d135034 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133928, d135034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133928, d135034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133929 q = 0) : d135035 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133929, d135035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133929, d135035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133930 q = 0) : d135036 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133930, d135036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133930, d135036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133931 q = 0) : d135037 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133931, d135037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133931, d135037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133932 q = 0) : d135038 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133932, d135038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133932, d135038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11473 (p : Pattern) (selected : d133934 p = 0) : d135040 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86922 q = 0) : d88037 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86922, d88037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86922, d88037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro618 q selected
  have h2 (q : Pattern) (selected : d86923 q = 0) : d88038 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86923, d88038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86923, d88038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86932 q = 0) : d88047 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86932, d88047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86932, d88047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133933 q = 0) : d135039 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133933, d135039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133933, d135039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133934 q = 0) : d135040 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133934, d135040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133934, d135040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11474 (p : Pattern) (selected : d133940 p = 0) : d135046 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133927 q = 0) : d135033 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133927, d135033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11471 q selected
    | true =>
      simp only [d133927, d135033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133928 q = 0) : d135034 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133928, d135034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133928, d135034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133935 q = 0) : d135041 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133935, d135041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11473 q selected
    | true =>
      simp only [d133935, d135041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133936 q = 0) : d135042 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133936, d135042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133936, d135042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133937 q = 0) : d135043 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133937, d135043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133937, d135043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133938 q = 0) : d135044 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133938, d135044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133938, d135044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133939 q = 0) : d135045 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133939, d135045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133939, d135045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133940 q = 0) : d135046 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133940, d135046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133940, d135046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11475 (p : Pattern) (selected : d133943 p = 0) : d135032 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86941 q = 0) : d88031 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86941, d88031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86941, d88031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro625 q selected
  have h2 (q : Pattern) (selected : d86942 q = 0) : d88032 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86942, d88032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86942, d88032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86943 q = 0) : d88037 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86943, d88037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86943, d88037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro626 q selected
  have h4 (q : Pattern) (selected : d86944 q = 0) : d88038 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86944, d88038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86944, d88038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86945 q = 0) : d88039 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86945, d88039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86945, d88039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d86949 q = 0) : d88047 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86949, d88047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d86949, d88047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133942 q = 0) : d135031 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133942, d135031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133942, d135031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133943 q = 0) : d135032 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133943, d135032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133943, d135032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11476 (p : Pattern) (selected : d133947 p = 0) : d135040 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86943 q = 0) : d88037 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86943, d88037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86943, d88037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro626 q selected
  have h2 (q : Pattern) (selected : d86944 q = 0) : d88038 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86944, d88038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86944, d88038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86949 q = 0) : d88047 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86949, d88047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86949, d88047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133946 q = 0) : d135039 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133946, d135039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133946, d135039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133947 q = 0) : d135040 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133947, d135040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133947, d135040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11477 (p : Pattern) (selected : d133953 p = 0) : d135046 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133944 q = 0) : d135033 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133944, d135033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11475 q selected
    | true =>
      simp only [d133944, d135033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133945 q = 0) : d135034 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133945, d135034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133945, d135034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133948 q = 0) : d135041 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133948, d135041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11476 q selected
    | true =>
      simp only [d133948, d135041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133949 q = 0) : d135042 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133949, d135042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133949, d135042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133950 q = 0) : d135043 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133950, d135043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133950, d135043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133951 q = 0) : d135044 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133951, d135044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133951, d135044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d133952 q = 0) : d135045 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133952, d135045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133952, d135045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d133953 q = 0) : d135046 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133953, d135046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133953, d135046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro11478 (p : Pattern) (selected : d133957 p = 0) : d135051 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133948 q = 0) : d135041 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133948, d135041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11476 q selected
    | true =>
      simp only [d133948, d135041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133949 q = 0) : d135042 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133949, d135042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133949, d135042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133954 q = 0) : d135048 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133954, d135048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133954, d135048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133955 q = 0) : d135049 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133955, d135049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133955, d135049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133956 q = 0) : d135050 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133956, d135050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133956, d135050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133957 q = 0) : d135051 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133957, d135051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133957, d135051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11479 (p : Pattern) (selected : d133964 p = 0) : d135058 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d86916 q = 0) : d88031 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86916, d88031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86916, d88031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro617 q selected
  have h2 (q : Pattern) (selected : d86917 q = 0) : d88032 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86917, d88032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86917, d88032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d86922 q = 0) : d88037 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d86922, d88037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86922, d88037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro618 q selected
  have h4 (q : Pattern) (selected : d86923 q = 0) : d88038 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d86923, d88038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d86923, d88038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d86924 q = 0) : d88039 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d86924, d88039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d86924, d88039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133960 q = 0) : d135054 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d133960, d135054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133960, d135054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3412 q selected
  have h7 (q : Pattern) (selected : d133961 q = 0) : d135055 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d133961, d135055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133961, d135055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133962 q = 0) : d135056 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d133962, d135056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d133962, d135056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d133963 q = 0) : d135057 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d133963, d135057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133963, d135057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133964 q = 0) : d135058 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d133964, d135058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d133964, d135058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro11480 (p : Pattern) (selected : d133970 p = 0) : d135064 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133965 q = 0) : d135059 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133965, d135059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11479 q selected
    | true =>
      simp only [d133965, d135059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133966 q = 0) : d135060 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133966, d135060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133966, d135060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133967 q = 0) : d135061 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133967, d135061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133967, d135061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133968 q = 0) : d135062 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133968, d135062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133968, d135062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133969 q = 0) : d135063 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133969, d135063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133969, d135063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133970 q = 0) : d135064 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133970, d135064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133970, d135064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11481 (p : Pattern) (selected : d133976 p = 0) : d135070 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133941 q = 0) : d135047 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133941, d135047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11472 q selected
    | true =>
      simp only [d133941, d135047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11474 q selected
  have h2 (q : Pattern) (selected : d133958 q = 0) : d135052 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133958, d135052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11477 q selected
    | true =>
      simp only [d133958, d135052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11478 q selected
  have h3 (q : Pattern) (selected : d133959 q = 0) : d135053 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133959, d135053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133959, d135053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133971 q = 0) : d135065 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133971, d135065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11480 q selected
    | true =>
      simp only [d133971, d135065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133972 q = 0) : d135066 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133972, d135066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133972, d135066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133973 q = 0) : d135067 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133973, d135067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133973, d135067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133974 q = 0) : d135068 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133974, d135068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133974, d135068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d133975 q = 0) : d135069 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133975, d135069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133975, d135069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133976 q = 0) : d135070 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133976, d135070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133976, d135070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro11482 (p : Pattern) (selected : d133981 p = 0) : d135051 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133935 q = 0) : d135041 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d133935, d135041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11473 q selected
    | true =>
      simp only [d133935, d135041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133936 q = 0) : d135042 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d133936, d135042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133936, d135042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133978 q = 0) : d135048 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d133978, d135048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133978, d135048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133979 q = 0) : d135049 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d133979, d135049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133979, d135049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133980 q = 0) : d135050 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d133980, d135050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d133980, d135050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d133981 q = 0) : d135051 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d133981, d135051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133981, d135051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11483 (p : Pattern) (selected : d133987 p = 0) : d135077 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133982 q = 0) : d135072 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d133982, d135072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11482 q selected
    | true =>
      simp only [d133982, d135072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d133983 q = 0) : d135073 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d133983, d135073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133983, d135073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133984 q = 0) : d135074 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d133984, d135074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133984, d135074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d133985 q = 0) : d135075 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d133985, d135075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133985, d135075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133986 q = 0) : d135076 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d133986, d135076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133986, d135076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133987 q = 0) : d135077 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d133987, d135077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133987, d135077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11484 (p : Pattern) (selected : d133993 p = 0) : d135083 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133796 q = 0) : d134922 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133796, d134922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133796, d134922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11440 q selected
  have h2 (q : Pattern) (selected : d133797 q = 0) : d134923 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133797, d134923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133797, d134923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d133806 q = 0) : d134932 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133806, d134932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11440 q selected
    | true =>
      simp only [d133806, d134932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11443 q selected
  have h4 (q : Pattern) (selected : d133807 q = 0) : d134933 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133807, d134933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133807, d134933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d133808 q = 0) : d134934 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133808, d134934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d133808, d134934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133894 q = 0) : d135000 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133894, d135000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11456 q selected
    | true =>
      simp only [d133894, d135000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11465 q selected
  have h7 (q : Pattern) (selected : d133907 q = 0) : d135013 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133907, d135013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11466 q selected
    | true =>
      simp only [d133907, d135013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11467 q selected
  have h8 (q : Pattern) (selected : d133908 q = 0) : d135014 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133908, d135014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133908, d135014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133909 q = 0) : d135015 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133909, d135015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d133909, d135015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d133910 q = 0) : d135016 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133910, d135016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d133910, d135016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d133914 q = 0) : d135020 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133914, d135020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133914, d135020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11468 q selected
  have h12 (q : Pattern) (selected : d133916 q = 0) : d135022 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133916, d135022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133916, d135022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11469 q selected
  have h13 (q : Pattern) (selected : d133917 q = 0) : d135023 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133917, d135023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d133917, d135023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d133918 q = 0) : d135024 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133918, d135024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d133918, d135024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d133919 q = 0) : d135025 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133919, d135025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d133919, d135025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d133920 q = 0) : d135026 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d133920, d135026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d133920, d135026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d133977 q = 0) : d135071 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133977, d135071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133977, d135071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11481 q selected
  have h18 (q : Pattern) (selected : d133988 q = 0) : d135078 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d133988, d135078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133988, d135078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11483 q selected
  have h19 (q : Pattern) (selected : d133989 q = 0) : d135079 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d133989, d135079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d133989, d135079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d133990 q = 0) : d135080 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d133990, d135080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d133990, d135080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d133991 q = 0) : d135081 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d133991, d135081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d133991, d135081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d133992 q = 0) : d135082 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d133992, d135082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d133992, d135082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d133993 q = 0) : d135083 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d133993, d135083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d133993, d135083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro11485 (p : Pattern) (selected : d133999 p = 0) : d135089 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d133994 q = 0) : d135084 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d133994, d135084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133994, d135084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11484 q selected
  have h2 (q : Pattern) (selected : d133995 q = 0) : d135085 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d133995, d135085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133995, d135085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d133996 q = 0) : d135086 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d133996, d135086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133996, d135086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133997 q = 0) : d135087 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d133997, d135087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133997, d135087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d133998 q = 0) : d135088 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d133998, d135088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133998, d135088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133999 q = 0) : d135089 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d133999, d135089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133999, d135089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11486 (p : Pattern) (selected : d134005 p = 0) : d135095 p = 1 := by
  have h0 (q : Pattern) (selected : d133086 q = 0) : d134320 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d133086, d134320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11257 q selected
    | true =>
      simp only [d133086, d134320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11285 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d133313 q = 0) : d134511 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d133313, d134511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133313, d134511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11335 q selected
  have h3 (q : Pattern) (selected : d133314 q = 0) : d134512 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d133314, d134512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d133314, d134512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d133541 q = 0) : d134703 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d133541, d134703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133541, d134703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11385 q selected
  have h5 (q : Pattern) (selected : d133542 q = 0) : d134704 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d133542, d134704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133542, d134704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d133543 q = 0) : d134705 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d133543, d134705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d133543, d134705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d133770 q = 0) : d134896 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d133770, d134896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133770, d134896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11435 q selected
  have h8 (q : Pattern) (selected : d133771 q = 0) : d134897 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d133771, d134897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133771, d134897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d133772 q = 0) : d134898 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d133772, d134898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d133772, d134898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d133773 q = 0) : d134899 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d133773, d134899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d133773, d134899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d134000 q = 0) : d135090 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d134000, d135090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134000, d135090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11485 q selected
  have h12 (q : Pattern) (selected : d134001 q = 0) : d135091 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d134001, d135091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134001, d135091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d134002 q = 0) : d135092 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d134002, d135092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134002, d135092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d134003 q = 0) : d135093 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d134003, d135093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134003, d135093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d134004 q = 0) : d135094 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d134004, d135094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d134004, d135094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d134005 q = 0) : d135095 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d134005, d135095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d134005, d135095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro11487 (p : Pattern) (selected : d134011 p = 0) : d135101 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d134006 q = 0) : d135096 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d134006, d135096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11486 q selected
    | true =>
      simp only [d134006, d135096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d134007 q = 0) : d135097 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d134007, d135097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134007, d135097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d134008 q = 0) : d135098 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d134008, d135098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d134008, d135098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d134009 q = 0) : d135099 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d134009, d135099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d134009, d135099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d134010 q = 0) : d135100 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d134010, d135100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d134010, d135100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d134011 q = 0) : d135101 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d134011, d135101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d134011, d135101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11488 (p : Pattern) (selected : d134017 p = 0) : d135107 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d134012 q = 0) : d135102 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d134012, d135102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11487 q selected
    | true =>
      simp only [d134012, d135102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d134013 q = 0) : d135103 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d134013, d135103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134013, d135103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d134014 q = 0) : d135104 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d134014, d135104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d134014, d135104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d134015 q = 0) : d135105 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d134015, d135105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d134015, d135105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d134016 q = 0) : d135106 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d134016, d135106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d134016, d135106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d134017 q = 0) : d135107 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d134017, d135107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d134017, d135107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11489 (p : Pattern) (selected : d134023 p = 0) : d135113 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d134018 q = 0) : d135108 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d134018, d135108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11488 q selected
    | true =>
      simp only [d134018, d135108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d134019 q = 0) : d135109 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d134019, d135109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134019, d135109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d134020 q = 0) : d135110 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d134020, d135110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d134020, d135110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d134021 q = 0) : d135111 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d134021, d135111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d134021, d135111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d134022 q = 0) : d135112 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d134022, d135112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d134022, d135112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d134023 q = 0) : d135113 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d134023, d135113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d134023, d135113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11490 (p : Pattern) (selected : d134028 p = 0) : d135118 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d134024 q = 0) : d135114 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d134024, d135114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11489 q selected
    | true =>
      simp only [d134024, d135114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d134025 q = 0) : d135115 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d134025, d135115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134025, d135115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d134026 q = 0) : d135116 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d134026, d135116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d134026, d135116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d134027 q = 0) : d135117 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d134027, d135117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d134027, d135117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d134028 q = 0) : d135118 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d134028, d135118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d134028, d135118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11491 (p : Pattern) (selected : d134034 p = 0) : d135124 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d134029 q = 0) : d135119 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d134029, d135119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11490 q selected
    | true =>
      simp only [d134029, d135119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d134030 q = 0) : d135120 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d134030, d135120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134030, d135120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d134031 q = 0) : d135121 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d134031, d135121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d134031, d135121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d134032 q = 0) : d135122 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d134032, d135122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d134032, d135122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d134033 q = 0) : d135123 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d134033, d135123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d134033, d135123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d134034 q = 0) : d135124 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d134034, d135124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d134034, d135124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11492 (p : Pattern) (selected : d134040 p = 0) : d135130 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d134035 q = 0) : d135125 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d134035, d135125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11491 q selected
    | true =>
      simp only [d134035, d135125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d134036 q = 0) : d135126 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d134036, d135126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134036, d135126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d134037 q = 0) : d135127 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d134037, d135127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d134037, d135127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d134038 q = 0) : d135128 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d134038, d135128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d134038, d135128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d134039 q = 0) : d135129 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d134039, d135129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d134039, d135129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d134040 q = 0) : d135130 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d134040, d135130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d134040, d135130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11493 (p : Pattern) (selected : d134046 p = 0) : d135136 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d134041 q = 0) : d135131 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d134041, d135131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11492 q selected
    | true =>
      simp only [d134041, d135131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d134042 q = 0) : d135132 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d134042, d135132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d134042, d135132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d134043 q = 0) : d135133 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d134043, d135133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d134043, d135133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d134044 q = 0) : d135134 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d134044, d135134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d134044, d135134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d134045 q = 0) : d135135 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d134045, d135135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d134045, d135135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d134046 q = 0) : d135136 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d134046, d135136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d134046, d135136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11494 (p : Pattern) (selected : d132866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d85823 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d85823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2 q selected
  have h2 (q : Pattern) (selected : d85824 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d85824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d85824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d85825 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d85825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d85825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132865 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d132865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d132865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d132866 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d132866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d132866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro11495 (p : Pattern) (selected : d132872 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d132867 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11494 q selected
    | true =>
      simp only [d132867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d132868 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132869 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d132869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132870 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d132870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d132870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d132871 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d132871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d132871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d132872 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d132872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro11496 (p : Pattern) (selected : d132878 p = 1) : d135141 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d132849 q = 1) : d132849 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d132855 q = 1) : d132855 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d132864 q = 1) : d132864 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d132873 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11495 q selected
    | true =>
      simp only [d132873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d132874 q = 1) : d135137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132874, d135137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d132874, d135137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132782 q = 1) : d132782 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d132875 q = 1) : d135138 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132875, d135138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d132875, d135138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d132876 q = 1) : d135139 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132876, d135139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132876, d135139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d132877 q = 1) : d135140 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132877, d135140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d132877, d135140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d132878 q = 1) : d135141 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132878, d135141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132878, d135141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro11497 (p : Pattern) (selected : d132890 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d132867 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d132867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11494 q selected
    | true =>
      simp only [d132867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d132868 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d132868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d132869 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d132869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d132870 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d132870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d132870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d132871 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d132871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d132871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d132890 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d132890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d132890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro11498 (p : Pattern) (selected : d132896 p = 1) : d135146 p = 1 := by
  have h0 (q : Pattern) (selected : d132849 q = 1) : d132849 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d132855 q = 1) : d132855 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d132864 q = 1) : d132864 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d132873 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11495 q selected
    | true =>
      simp only [d132873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d132874 q = 1) : d135137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132874, d135137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d132874, d135137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132782 q = 1) : d132782 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d132875 q = 1) : d135138 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132875, d135138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d132875, d135138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d132876 q = 1) : d135139 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132876, d135139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d132876, d135139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d132877 q = 1) : d135140 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132877, d135140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132877, d135140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d132883 q = 1) : d132883 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d132887 q = 1) : d132887 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d132889 q = 1) : d132889 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d132891 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11497 q selected
    | true =>
      simp only [d132891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d132892 q = 1) : d135142 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132892, d135142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d132892, d135142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d132789 q = 1) : d132789 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d132893 q = 1) : d135143 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132893, d135143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d132893, d135143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d132894 q = 1) : d135144 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132894, d135144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d132894, d135144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d132895 q = 1) : d135145 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132895, d135145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d132895, d135145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d132896 q = 1) : d135146 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132896, d135146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d132896, d135146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro11499 (p : Pattern) (selected : d132905 p = 1) : d135153 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d132889 q = 1) : d132889 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d132891 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d132891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11497 q selected
    | true =>
      simp only [d132891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d132892 q = 1) : d135142 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132892, d135142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d132892, d135142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d132789 q = 1) : d132789 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d132893 q = 1) : d135143 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132893, d135143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d132893, d135143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d132903 q = 1) : d135151 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132903, d135151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132903, d135151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d132904 q = 1) : d135152 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132904, d135152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132904, d135152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d132905 q = 1) : d135153 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132905, d135153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d132905, d135153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
end NetHack.Soko22Hazard87
