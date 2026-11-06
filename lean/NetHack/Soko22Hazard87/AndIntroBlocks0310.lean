import NetHack.Soko22Hazard87.AndIntroBlocks0309
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro77500 (p : Pattern) (ha : d261985 p = 1) (hb : d282107 p = 1) : d299923 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d282102 q = 1) : d299918 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d282102, d299918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76897 q hb ha
    | true =>
      simp only [d282102, d299918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76867 q hb ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d282103 q = 1) : d299919 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d282103, d299919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282103, d299919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d282104 q = 1) : d299920 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d282104, d299920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d282104, d299920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d282105 q = 1) : d299921 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282105, d299921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282105, d299921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d282106 q = 1) : d299922 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d282106, d299922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282106, d299922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d282107 q = 1) : d299923 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d282107, d299923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282107, d299923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77501 (p : Pattern) (ha : d261985 p = 1) (hb : d282113 p = 1) : d299929 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30946 q = 1) (hb : d261985 q = 1) : d298337 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30946, d298337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76859 q ha hb
    | true =>
      simp only [d30946, d298337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76862 q ha hb
  have h2 (q : Pattern) (ha : d30947 q = 1) (hb : d261985 q = 1) : d298338 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d30947, d298338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30947, d298338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d282094 q = 1) : d299910 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282094, d299910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d282094, d299910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d282095 q = 1) : d299911 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282095, d299911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282095, d299911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d282097 q = 1) : d299913 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d282097, d299913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282097, d299913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77499 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d282098 q = 1) : d299914 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d282098, d299914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d282098, d299914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d261985 q = 1) (hb : d282099 q = 1) : d299915 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282099, d299915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d282099, d299915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d261985 q = 1) (hb : d282100 q = 1) : d299916 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282100, d299916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d282100, d299916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d261985 q = 1) (hb : d282101 q = 1) : d299917 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d282101, d299917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d282101, d299917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d261985 q = 1) (hb : d282108 q = 1) : d299924 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d282108, d299924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282108, d299924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77500 q ha hb
  have h11 (q : Pattern) (ha : d261985 q = 1) (hb : d282109 q = 1) : d299925 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d282109, d299925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d282109, d299925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d261985 q = 1) (hb : d282110 q = 1) : d299926 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282110, d299926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d282110, d299926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d261985 q = 1) (hb : d282111 q = 1) : d299927 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282111, d299927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d282111, d299927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d261985 q = 1) (hb : d282112 q = 1) : d299928 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d282112, d299928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d282112, d299928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d261985 q = 1) (hb : d282113 q = 1) : d299929 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d282113, d299929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d282113, d299929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro77502 (p : Pattern) (ha : d261985 p = 1) (hb : d282119 p = 1) : d299935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d282114 q = 1) : d299930 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d282114, d299930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282114, d299930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77501 q ha hb
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d282115 q = 1) : d299931 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d282115, d299931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282115, d299931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d282116 q = 1) : d299932 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d282116, d299932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282116, d299932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d282117 q = 1) : d299933 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d282117, d299933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282117, d299933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d282118 q = 1) : d299934 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d282118, d299934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282118, d299934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d282119 q = 1) : d299935 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d282119, d299935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282119, d299935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77503 (p : Pattern) (ha : d261985 p = 1) (hb : d282123 p = 1) : d299939 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31276 q = 1) (hb : d261985 q = 1) : d298581 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31276, d298581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76911 q ha hb
    | true =>
      simp only [d31276, d298581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76912 q ha hb
  have h2 (q : Pattern) (ha : d31277 q = 1) (hb : d261985 q = 1) : d298582 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31277, d298582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31277, d298582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31278 q = 1) (hb : d261985 q = 1) : d298583 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31278, d298583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31278, d298583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31279 q = 1) (hb : d261985 q = 1) : d298584 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31279, d298584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31279, d298584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31280 q = 1) (hb : d261985 q = 1) : d298585 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31280, d298585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31280, d298585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d282123 q = 1) : d299939 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d282123, d299939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282123, d299939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro77504 (p : Pattern) (ha : d261985 p = 1) (hb : d282134 p = 1) : d299950 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d282129 q = 1) : d299945 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d282129, d299945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76951 q hb ha
    | true =>
      simp only [d282129, d299945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76920 q hb ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d282130 q = 1) : d299946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d282130, d299946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282130, d299946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d282131 q = 1) : d299947 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d282131, d299947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d282131, d299947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d282132 q = 1) : d299948 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282132, d299948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282132, d299948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d282133 q = 1) : d299949 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d282133, d299949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282133, d299949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d282134 q = 1) : d299950 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d282134, d299950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282134, d299950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77505 (p : Pattern) (ha : d261985 p = 1) (hb : d282140 p = 1) : d299956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31282 q = 1) (hb : d261985 q = 1) : d298587 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31282, d298587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76910 q ha hb
    | true =>
      simp only [d31282, d298587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76913 q ha hb
  have h2 (q : Pattern) (ha : d31283 q = 1) (hb : d261985 q = 1) : d298588 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d31283, d298588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31283, d298588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d282121 q = 1) : d299937 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282121, d299937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d282121, d299937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d282122 q = 1) : d299938 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282122, d299938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282122, d299938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d282124 q = 1) : d299940 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d282124, d299940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282124, d299940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77503 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d282125 q = 1) : d299941 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d282125, d299941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d282125, d299941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d261985 q = 1) (hb : d282126 q = 1) : d299942 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282126, d299942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d282126, d299942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d261985 q = 1) (hb : d282127 q = 1) : d299943 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282127, d299943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d282127, d299943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d261985 q = 1) (hb : d282128 q = 1) : d299944 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d282128, d299944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d282128, d299944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d261985 q = 1) (hb : d282135 q = 1) : d299951 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d282135, d299951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282135, d299951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77504 q ha hb
  have h11 (q : Pattern) (ha : d261985 q = 1) (hb : d282136 q = 1) : d299952 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d282136, d299952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d282136, d299952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d261985 q = 1) (hb : d282137 q = 1) : d299953 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d282137, d299953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d282137, d299953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d261985 q = 1) (hb : d282138 q = 1) : d299954 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d282138, d299954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d282138, d299954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d261985 q = 1) (hb : d282139 q = 1) : d299955 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d282139, d299955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d282139, d299955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d261985 q = 1) (hb : d282140 q = 1) : d299956 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d282140, d299956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d282140, d299956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro77506 (p : Pattern) (ha : d261985 p = 1) (hb : d282146 p = 1) : d299962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d282141 q = 1) : d299957 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d282141, d299957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282141, d299957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77505 q ha hb
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d282142 q = 1) : d299958 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d282142, d299958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282142, d299958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d282143 q = 1) : d299959 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d282143, d299959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282143, d299959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d282144 q = 1) : d299960 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d282144, d299960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282144, d299960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d282145 q = 1) : d299961 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d282145, d299961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282145, d299961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d282146 q = 1) : d299962 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d282146, d299962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d282146, d299962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77507 (p : Pattern) (ha : d261985 p = 1) (hb : d290378 p = 1) : d299967 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31710 q = 1) (hb : d261985 q = 1) : d298895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31710, d298895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76970 q ha hb
    | true =>
      simp only [d31710, d298895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76971 q ha hb
  have h2 (q : Pattern) (ha : d31711 q = 1) (hb : d261985 q = 1) : d298896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31711, d298896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31711, d298896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31712 q = 1) (hb : d261985 q = 1) : d298897 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31712, d298897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31712, d298897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31713 q = 1) (hb : d261985 q = 1) : d298898 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31713, d298898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31713, d298898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31714 q = 1) (hb : d261985 q = 1) : d298899 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31714, d298899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31714, d298899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d290378 q = 1) : d299967 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290378, d299967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290378, d299967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro77508 (p : Pattern) (ha : d261985 p = 1) (hb : d290389 p = 1) : d299978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d290384 q = 1) : d299973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290384, d299973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77011 q hb ha
    | true =>
      simp only [d290384, d299973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76979 q hb ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d290385 q = 1) : d299974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290385, d299974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290385, d299974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d290386 q = 1) : d299975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290386, d299975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290386, d299975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d290387 q = 1) : d299976 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290387, d299976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290387, d299976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d290388 q = 1) : d299977 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290388, d299977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290388, d299977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d290389 q = 1) : d299978 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290389, d299978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290389, d299978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77509 (p : Pattern) (ha : d261985 p = 1) (hb : d290395 p = 1) : d299984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31716 q = 1) (hb : d261985 q = 1) : d298901 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31716, d298901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76969 q ha hb
    | true =>
      simp only [d31716, d298901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76972 q ha hb
  have h2 (q : Pattern) (ha : d31717 q = 1) (hb : d261985 q = 1) : d298902 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d31717, d298902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31717, d298902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d290376 q = 1) : d299965 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290376, d299965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d290376, d299965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d290377 q = 1) : d299966 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290377, d299966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290377, d299966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d290379 q = 1) : d299968 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290379, d299968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290379, d299968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77507 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d290380 q = 1) : d299969 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290380, d299969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290380, d299969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d261985 q = 1) (hb : d290381 q = 1) : d299970 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290381, d299970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290381, d299970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d261985 q = 1) (hb : d290382 q = 1) : d299971 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290382, d299971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d290382, d299971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d261985 q = 1) (hb : d290383 q = 1) : d299972 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290383, d299972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290383, d299972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d261985 q = 1) (hb : d290390 q = 1) : d299979 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290390, d299979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290390, d299979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77508 q ha hb
  have h11 (q : Pattern) (ha : d261985 q = 1) (hb : d290391 q = 1) : d299980 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290391, d299980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290391, d299980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d261985 q = 1) (hb : d290392 q = 1) : d299981 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290392, d299981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d290392, d299981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d261985 q = 1) (hb : d290393 q = 1) : d299982 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290393, d299982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d290393, d299982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d261985 q = 1) (hb : d290394 q = 1) : d299983 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290394, d299983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290394, d299983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d261985 q = 1) (hb : d290395 q = 1) : d299984 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290395, d299984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290395, d299984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro77510 (p : Pattern) (ha : d261985 p = 1) (hb : d290401 p = 1) : d299990 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d290396 q = 1) : d299985 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290396, d299985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290396, d299985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77509 q ha hb
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d290397 q = 1) : d299986 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290397, d299986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290397, d299986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d290398 q = 1) : d299987 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290398, d299987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290398, d299987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d290399 q = 1) : d299988 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290399, d299988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290399, d299988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d290400 q = 1) : d299989 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290400, d299989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290400, d299989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d290401 q = 1) : d299990 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290401, d299990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290401, d299990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77511 (p : Pattern) (ha : d261985 p = 1) (hb : d290407 p = 1) : d299996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32242 q = 1) (hb : d261985 q = 1) : d299262 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32242, d299262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77033 q ha hb
    | true =>
      simp only [d32242, d299262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77034 q ha hb
  have h2 (q : Pattern) (ha : d32243 q = 1) (hb : d261985 q = 1) : d299263 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32243, d299263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32243, d299263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32244 q = 1) (hb : d261985 q = 1) : d299264 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32244, d299264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32244, d299264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32245 q = 1) (hb : d261985 q = 1) : d299265 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32245, d299265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32245, d299265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32246 q = 1) (hb : d261985 q = 1) : d299266 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32246, d299266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32246, d299266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d290407 q = 1) : d299996 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290407, d299996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290407, d299996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro77512 (p : Pattern) (ha : d261985 p = 1) (hb : d290418 p = 1) : d300007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d290413 q = 1) : d300002 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290413, d300002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77076 q hb ha
    | true =>
      simp only [d290413, d300002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77042 q hb ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d290414 q = 1) : d300003 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290414, d300003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290414, d300003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d290415 q = 1) : d300004 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290415, d300004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290415, d300004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d290416 q = 1) : d300005 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290416, d300005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290416, d300005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d290417 q = 1) : d300006 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290417, d300006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290417, d300006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d290418 q = 1) : d300007 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290418, d300007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290418, d300007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77513 (p : Pattern) (ha : d261985 p = 1) (hb : d290424 p = 1) : d300013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32248 q = 1) (hb : d261985 q = 1) : d299268 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d32248, d299268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77032 q ha hb
    | true =>
      simp only [d32248, d299268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77035 q ha hb
  have h2 (q : Pattern) (ha : d32249 q = 1) (hb : d261985 q = 1) : d299269 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d32249, d299269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32249, d299269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d290405 q = 1) : d299994 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290405, d299994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d290405, d299994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d290406 q = 1) : d299995 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290406, d299995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290406, d299995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d290408 q = 1) : d299997 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290408, d299997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290408, d299997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77511 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d290409 q = 1) : d299998 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290409, d299998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290409, d299998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d261985 q = 1) (hb : d290410 q = 1) : d299999 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290410, d299999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290410, d299999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d261985 q = 1) (hb : d290411 q = 1) : d300000 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290411, d300000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d290411, d300000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d261985 q = 1) (hb : d290412 q = 1) : d300001 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290412, d300001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290412, d300001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d261985 q = 1) (hb : d290419 q = 1) : d300008 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290419, d300008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290419, d300008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77512 q ha hb
  have h11 (q : Pattern) (ha : d261985 q = 1) (hb : d290420 q = 1) : d300009 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290420, d300009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290420, d300009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d261985 q = 1) (hb : d290421 q = 1) : d300010 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290421, d300010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d290421, d300010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d261985 q = 1) (hb : d290422 q = 1) : d300011 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290422, d300011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d290422, d300011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d261985 q = 1) (hb : d290423 q = 1) : d300012 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290423, d300012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290423, d300012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d261985 q = 1) (hb : d290424 q = 1) : d300013 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290424, d300013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290424, d300013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro77514 (p : Pattern) (ha : d261985 p = 1) (hb : d290430 p = 1) : d300019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d290425 q = 1) : d300014 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290425, d300014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290425, d300014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77513 q ha hb
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d290426 q = 1) : d300015 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290426, d300015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290426, d300015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d290427 q = 1) : d300016 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290427, d300016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290427, d300016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d290428 q = 1) : d300017 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290428, d300017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290428, d300017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d290429 q = 1) : d300018 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290429, d300018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290429, d300018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d290430 q = 1) : d300019 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290430, d300019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290430, d300019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77515 (p : Pattern) (ha : d261985 p = 1) (hb : d290437 p = 1) : d300026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32776 q = 1) (hb : d261985 q = 1) : d299600 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32776, d299600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77099 q ha hb
    | true =>
      simp only [d32776, d299600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77100 q ha hb
  have h2 (q : Pattern) (ha : d32777 q = 1) (hb : d261985 q = 1) : d299601 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32777, d299601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32777, d299601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32778 q = 1) (hb : d261985 q = 1) : d299602 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32778, d299602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32778, d299602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32779 q = 1) (hb : d261985 q = 1) : d299603 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32779, d299603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32779, d299603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32780 q = 1) (hb : d261985 q = 1) : d299604 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32780, d299604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32780, d299604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d290437 q = 1) : d300026 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290437, d300026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290437, d300026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro77516 (p : Pattern) (ha : d261985 p = 1) (hb : d290448 p = 1) : d300037 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d290443 q = 1) : d300032 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d290443, d300032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77139 q hb ha
    | true =>
      simp only [d290443, d300032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77108 q hb ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d290444 q = 1) : d300033 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d290444, d300033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290444, d300033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d290445 q = 1) : d300034 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d290445, d300034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290445, d300034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d290446 q = 1) : d300035 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d290446, d300035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290446, d300035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d290447 q = 1) : d300036 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290447, d300036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290447, d300036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d290448 q = 1) : d300037 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d290448, d300037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290448, d300037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77517 (p : Pattern) (ha : d261985 p = 1) (hb : d290454 p = 1) : d300043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32782 q = 1) (hb : d261985 q = 1) : d299606 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d32782, d299606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77098 q ha hb
    | true =>
      simp only [d32782, d299606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77101 q ha hb
  have h2 (q : Pattern) (ha : d32783 q = 1) (hb : d261985 q = 1) : d299607 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d32783, d299607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32783, d299607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d290435 q = 1) : d300024 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290435, d300024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d290435, d300024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d290436 q = 1) : d300025 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290436, d300025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290436, d300025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d290438 q = 1) : d300027 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290438, d300027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290438, d300027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77515 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d290439 q = 1) : d300028 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290439, d300028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290439, d300028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d261985 q = 1) (hb : d290440 q = 1) : d300029 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290440, d300029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290440, d300029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d261985 q = 1) (hb : d290441 q = 1) : d300030 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290441, d300030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d290441, d300030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d261985 q = 1) (hb : d290442 q = 1) : d300031 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290442, d300031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290442, d300031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d261985 q = 1) (hb : d290449 q = 1) : d300038 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d290449, d300038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290449, d300038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77516 q ha hb
  have h11 (q : Pattern) (ha : d261985 q = 1) (hb : d290450 q = 1) : d300039 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d290450, d300039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290450, d300039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d261985 q = 1) (hb : d290451 q = 1) : d300040 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d290451, d300040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d290451, d300040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d261985 q = 1) (hb : d290452 q = 1) : d300041 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d290452, d300041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d290452, d300041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d261985 q = 1) (hb : d290453 q = 1) : d300042 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d290453, d300042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d290453, d300042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d261985 q = 1) (hb : d290454 q = 1) : d300043 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d290454, d300043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d290454, d300043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro77518 (p : Pattern) (ha : d261985 p = 1) (hb : d290460 p = 1) : d300049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d290455 q = 1) : d300044 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d290455, d300044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290455, d300044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77517 q ha hb
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d290456 q = 1) : d300045 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d290456, d300045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290456, d300045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d290457 q = 1) : d300046 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d290457, d300046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290457, d300046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d290458 q = 1) : d300047 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d290458, d300047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290458, d300047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d290459 q = 1) : d300048 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d290459, d300048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290459, d300048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d290460 q = 1) : d300049 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d290460, d300049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d290460, d300049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77519 (p : Pattern) (ha : d261985 p = 1) (hb : d290466 p = 1) : d300055 p = 1 := by
  have h0 (q : Pattern) (ha : d261985 q = 1) (hb : d282120 q = 1) : d299936 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d282120, d299936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77498 q ha hb
    | true =>
      simp only [d282120, d299936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77502 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d282147 q = 1) : d299963 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d282147, d299963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d282147, d299963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77506 q ha hb
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d282148 q = 1) : d299964 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d282148, d299964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282148, d299964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d290402 q = 1) : d299991 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290402, d299991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290402, d299991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77510 q ha hb
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d290403 q = 1) : d299992 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d290403, d299992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290403, d299992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d290404 q = 1) : d299993 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d290404, d299993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290404, d299993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d261985 q = 1) (hb : d290431 q = 1) : d300020 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290431, d300020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290431, d300020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77514 q ha hb
  have h8 (q : Pattern) (ha : d261985 q = 1) (hb : d290432 q = 1) : d300021 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d290432, d300021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290432, d300021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d261985 q = 1) (hb : d290433 q = 1) : d300022 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d290433, d300022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290433, d300022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d261985 q = 1) (hb : d290434 q = 1) : d300023 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d290434, d300023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d290434, d300023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d261985 q = 1) (hb : d290461 q = 1) : d300050 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d290461, d300050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290461, d300050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77518 q ha hb
  have h12 (q : Pattern) (ha : d261985 q = 1) (hb : d290462 q = 1) : d300051 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d290462, d300051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290462, d300051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d261985 q = 1) (hb : d290463 q = 1) : d300052 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d290463, d300052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290463, d300052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d261985 q = 1) (hb : d290464 q = 1) : d300053 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d290464, d300053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d290464, d300053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d261985 q = 1) (hb : d290465 q = 1) : d300054 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d290465, d300054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d290465, d300054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d261985 q = 1) (hb : d290466 q = 1) : d300055 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d290466, d300055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d290466, d300055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro77520 (p : Pattern) (ha : d261985 p = 1) (hb : d290472 p = 1) : d300061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d290467 q = 1) : d300056 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d290467, d300056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77519 q ha hb
    | true =>
      simp only [d290467, d300056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d290468 q = 1) : d300057 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d290468, d300057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290468, d300057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d290469 q = 1) : d300058 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d290469, d300058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290469, d300058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d290470 q = 1) : d300059 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d290470, d300059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290470, d300059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d290471 q = 1) : d300060 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d290471, d300060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290471, d300060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d290472 q = 1) : d300061 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d290472, d300061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290472, d300061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro77521 (p : Pattern) (ha : d261985 p = 1) (hb : d290478 p = 1) : d300067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d290473 q = 1) : d300062 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d290473, d300062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77520 q ha hb
    | true =>
      simp only [d290473, d300062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d290474 q = 1) : d300063 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d290474, d300063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290474, d300063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d290475 q = 1) : d300064 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d290475, d300064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290475, d300064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d290476 q = 1) : d300065 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d290476, d300065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290476, d300065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d290477 q = 1) : d300066 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d290477, d300066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290477, d300066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d290478 q = 1) : d300067 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d290478, d300067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290478, d300067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro77522 (p : Pattern) (ha : d261985 p = 1) (hb : d290484 p = 1) : d300073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d290479 q = 1) : d300068 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d290479, d300068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77521 q ha hb
    | true =>
      simp only [d290479, d300068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d290480 q = 1) : d300069 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d290480, d300069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290480, d300069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d290481 q = 1) : d300070 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d290481, d300070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290481, d300070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d290482 q = 1) : d300071 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d290482, d300071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290482, d300071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d290483 q = 1) : d300072 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d290483, d300072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290483, d300072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d290484 q = 1) : d300073 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d290484, d300073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290484, d300073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro77523 (p : Pattern) (ha : d261985 p = 1) (hb : d290490 p = 1) : d300079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d290485 q = 1) : d300074 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d290485, d300074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77522 q ha hb
    | true =>
      simp only [d290485, d300074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d290486 q = 1) : d300075 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d290486, d300075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290486, d300075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d290487 q = 1) : d300076 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d290487, d300076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290487, d300076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d290488 q = 1) : d300077 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d290488, d300077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290488, d300077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d290489 q = 1) : d300078 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d290489, d300078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290489, d300078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d290490 q = 1) : d300079 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d290490, d300079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290490, d300079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro77524 (p : Pattern) (ha : d261985 p = 1) (hb : d290496 p = 1) : d300085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d290491 q = 1) : d300080 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d290491, d300080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77523 q ha hb
    | true =>
      simp only [d290491, d300080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d290492 q = 1) : d300081 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d290492, d300081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290492, d300081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d290493 q = 1) : d300082 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d290493, d300082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290493, d300082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d290494 q = 1) : d300083 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d290494, d300083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290494, d300083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d290495 q = 1) : d300084 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d290495, d300084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290495, d300084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d290496 q = 1) : d300085 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d290496, d300085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290496, d300085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro77525 (p : Pattern) (ha : d261985 p = 1) (hb : d290502 p = 1) : d300091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d290497 q = 1) : d300086 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d290497, d300086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77524 q ha hb
    | true =>
      simp only [d290497, d300086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d290498 q = 1) : d300087 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d290498, d300087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290498, d300087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d290499 q = 1) : d300088 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d290499, d300088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290499, d300088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d290500 q = 1) : d300089 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d290500, d300089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290500, d300089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d290501 q = 1) : d300090 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d290501, d300090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290501, d300090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d290502 q = 1) : d300091 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d290502, d300091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290502, d300091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro77526 (p : Pattern) (ha : d261985 p = 1) (hb : d290508 p = 1) : d300097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d261985 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d261985 q = 1) (hb : d290503 q = 1) : d300092 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d290503, d300092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77525 q ha hb
    | true =>
      simp only [d290503, d300092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d261985 q = 1) (hb : d290504 q = 1) : d300093 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d290504, d300093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d290504, d300093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d261985 q = 1) (hb : d290505 q = 1) : d300094 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d290505, d300094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d290505, d300094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d261985 q = 1) (hb : d290506 q = 1) : d300095 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d290506, d300095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d290506, d300095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d261985 q = 1) (hb : d290507 q = 1) : d300096 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d290507, d300096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d290507, d300096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d261985 q = 1) (hb : d290508 q = 1) : d300097 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d290508, d300097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d290508, d300097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro77527 (p : Pattern) (ha : d262145 p = 1) (hb : d298159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262093 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262099 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d262134 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d262013 q = 1) (hb : d298095 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262013, d298095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77158 q ha hb
    | true =>
      simp only [d262013, d298095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d262135 q = 1) (hb : d298155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262135, d298155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d262135, d298155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d262141 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d262142 q = 1) (hb : d298156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262142, d298156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d262142, d298156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d262143 q = 1) (hb : d298157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262143, d298157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262143, d298157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d262144 q = 1) (hb : d298158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262144, d298158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262144, d298158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d262145 q = 1) (hb : d298159 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262145, d298159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262145, d298159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro77528 (p : Pattern) (ha : d262164 p = 1) (hb : d298166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262134 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262013 q = 1) (hb : d298095 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262013, d298095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77158 q ha hb
    | true =>
      simp only [d262013, d298095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d262135 q = 1) (hb : d298155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262135, d298155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262135, d298155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d262141 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d262142 q = 1) (hb : d298156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262142, d298156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d262142, d298156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d262143 q = 1) (hb : d298157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262143, d298157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262143, d298157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262144 q = 1) (hb : d298158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262144, d298158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262144, d298158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d262150 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d262154 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d262156 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d262020 q = 1) (hb : d298102 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262020, d298102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77160 q ha hb
    | true =>
      simp only [d262020, d298102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d262157 q = 1) (hb : d298162 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262157, d298162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d262157, d298162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262160 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262161 q = 1) (hb : d298163 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262161, d298163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262161, d298163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262162 q = 1) (hb : d298164 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262162, d298164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d262162, d298164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d262163 q = 1) (hb : d298165 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262163, d298165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d262163, d298165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d262164 q = 1) (hb : d298166 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262164, d298166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d262164, d298166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro77529 (p : Pattern) (ha : d262173 p = 1) (hb : d299887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262156 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262020 q = 1) (hb : d298102 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262020, d298102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77160 q ha hb
    | true =>
      simp only [d262020, d298102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d262157 q = 1) (hb : d298162 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262157, d298162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262157, d298162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262160 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262161 q = 1) (hb : d298163 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262161, d298163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262161, d298163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262171 q = 1) (hb : d298164 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262171, d298164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262171, d298164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262172 q = 1) (hb : d298165 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262172, d298165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262172, d298165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262173 q = 1) (hb : d299887 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262173, d299887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262173, d299887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77530 (p : Pattern) (ha : d262213 p = 1) (hb : d299897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262202 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262056 q = 1) (hb : d298138 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262056, d298138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77165 q ha hb
    | true =>
      simp only [d262056, d298138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d262203 q = 1) (hb : d299893 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262203, d299893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262203, d299893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262209 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262210 q = 1) (hb : d299894 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262210, d299894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262210, d299894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262211 q = 1) (hb : d299895 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262211, d299895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262211, d299895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262212 q = 1) (hb : d299896 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262212, d299896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262212, d299896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262213 q = 1) (hb : d299897 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262213, d299897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262213, d299897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77531 (p : Pattern) (ha : d262219 p = 1) (hb : d299903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262087 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262165 q = 1) (hb : d298167 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262165, d298167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77527 q ha hb
    | true =>
      simp only [d262165, d298167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77528 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262167 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262168 q = 1) (hb : d298168 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262168, d298168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d262168, d298168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262169 q = 1) (hb : d299885 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262169, d299885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262169, d299885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262170 q = 1) (hb : d299886 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262170, d299886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262170, d299886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262174 q = 1) (hb : d299888 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262174, d299888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262174, d299888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77529 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d262175 q = 1) (hb : d299889 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262175, d299889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d262175, d299889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d262176 q = 1) (hb : d299890 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262176, d299890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d262176, d299890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d262177 q = 1) (hb : d299891 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262177, d299891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d262177, d299891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d262178 q = 1) (hb : d299892 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262178, d299892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d262178, d299892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d262214 q = 1) (hb : d299898 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262214, d299898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262214, d299898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77530 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262215 q = 1) (hb : d299899 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262215, d299899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262215, d299899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262216 q = 1) (hb : d299900 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262216, d299900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d262216, d299900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d262217 q = 1) (hb : d299901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262217, d299901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d262217, d299901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d262218 q = 1) (hb : d299902 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262218, d299902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d262218, d299902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d262219 q = 1) (hb : d299903 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d262219, d299903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d262219, d299903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro77532 (p : Pattern) (ha : d262225 p = 1) (hb : d299909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d262068 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d262068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d262068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66694 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d262069 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d262069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d262069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d262070 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d262070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d262070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d262071 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d262071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d262071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d262072 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d262072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d262072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262220 q = 1) (hb : d299904 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d262220, d299904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262220, d299904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77531 q ha hb
  have h8 (q : Pattern) (ha : d262221 q = 1) (hb : d299905 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d262221, d299905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262221, d299905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d262222 q = 1) (hb : d299906 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d262222, d299906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262222, d299906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d262223 q = 1) (hb : d299907 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d262223, d299907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262223, d299907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d262224 q = 1) (hb : d299908 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d262224, d299908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262224, d299908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d262225 q = 1) (hb : d299909 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d262225, d299909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d262225, d299909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro77533 (p : Pattern) (ha : d262339 p = 1) (hb : d298326 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262269 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262278 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d262328 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d262243 q = 1) (hb : d298321 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262243, d298321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77195 q ha hb
    | true =>
      simp only [d262243, d298321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77196 q ha hb
  have h5 (q : Pattern) (ha : d262329 q = 1) (hb : d298322 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262329, d298322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d262329, d298322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d262335 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d262336 q = 1) (hb : d298323 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262336, d298323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d262336, d298323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d262337 q = 1) (hb : d298324 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262337, d298324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262337, d298324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d262338 q = 1) (hb : d298325 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262338, d298325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262338, d298325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d262339 q = 1) (hb : d298326 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262339, d298326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262339, d298326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro77534 (p : Pattern) (ha : d262360 p = 1) (hb : d298336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262278 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262328 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262243 q = 1) (hb : d298321 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262243, d298321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77195 q ha hb
    | true =>
      simp only [d262243, d298321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77196 q ha hb
  have h4 (q : Pattern) (ha : d262329 q = 1) (hb : d298322 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262329, d298322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262329, d298322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d262335 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d262336 q = 1) (hb : d298323 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262336, d298323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d262336, d298323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d262337 q = 1) (hb : d298324 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262337, d298324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262337, d298324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262338 q = 1) (hb : d298325 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262338, d298325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262338, d298325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d262345 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d262350 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d262352 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d262253 q = 1) (hb : d298331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262253, d298331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77198 q ha hb
    | true =>
      simp only [d262253, d298331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77199 q ha hb
  have h13 (q : Pattern) (ha : d262353 q = 1) (hb : d298332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262353, d298332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d262353, d298332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262356 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262357 q = 1) (hb : d298333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262357, d298333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262357, d298333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262358 q = 1) (hb : d298334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262358, d298334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d262358, d298334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d262359 q = 1) (hb : d298335 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262359, d298335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d262359, d298335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d262360 q = 1) (hb : d298336 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262360, d298336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d262360, d298336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro77535 (p : Pattern) (ha : d262380 p = 1) (hb : d299912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262352 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262253 q = 1) (hb : d298331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262253, d298331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77198 q ha hb
    | true =>
      simp only [d262253, d298331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77199 q ha hb
  have h3 (q : Pattern) (ha : d262353 q = 1) (hb : d298332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262353, d298332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262353, d298332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262356 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262357 q = 1) (hb : d298333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262357, d298333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262357, d298333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262378 q = 1) (hb : d298334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262378, d298334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262378, d298334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262379 q = 1) (hb : d298335 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262379, d298335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262379, d298335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262380 q = 1) (hb : d299912 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262380, d299912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262380, d299912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77536 (p : Pattern) (ha : d262448 p = 1) (hb : d299923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262432 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262437 q = 1) (hb : d299918 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262437, d299918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77231 q ha hb
    | true =>
      simp only [d262437, d299918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77234 q ha hb
  have h3 (q : Pattern) (ha : d262438 q = 1) (hb : d299919 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262438, d299919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262438, d299919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262444 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262445 q = 1) (hb : d299920 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262445, d299920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262445, d299920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262446 q = 1) (hb : d299921 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262446, d299921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262446, d299921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262447 q = 1) (hb : d299922 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262447, d299922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262447, d299922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262448 q = 1) (hb : d299923 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262448, d299923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262448, d299923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77537 (p : Pattern) (ha : d262461 p = 1) (hb : d299929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262261 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262361 q = 1) (hb : d298337 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262361, d298337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77533 q ha hb
    | true =>
      simp only [d262361, d298337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77534 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262374 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262375 q = 1) (hb : d298338 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262375, d298338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d262375, d298338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262376 q = 1) (hb : d299910 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262376, d299910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262376, d299910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262377 q = 1) (hb : d299911 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262377, d299911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262377, d299911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262381 q = 1) (hb : d299913 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262381, d299913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262381, d299913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77535 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d262383 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d262384 q = 1) (hb : d299914 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262384, d299914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d262384, d299914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d262385 q = 1) (hb : d299915 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262385, d299915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d262385, d299915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d262386 q = 1) (hb : d299916 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262386, d299916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d262386, d299916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d262387 q = 1) (hb : d299917 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262387, d299917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d262387, d299917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d262449 q = 1) (hb : d299924 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262449, d299924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262449, d299924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77536 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262456 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262457 q = 1) (hb : d299925 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262457, d299925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262457, d299925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262458 q = 1) (hb : d299926 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262458, d299926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d262458, d299926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d262459 q = 1) (hb : d299927 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262459, d299927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d262459, d299927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d262460 q = 1) (hb : d299928 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262460, d299928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d262460, d299928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d262461 q = 1) (hb : d299929 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d262461, d299929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d262461, d299929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro77538 (p : Pattern) (ha : d262467 p = 1) (hb : d299935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262462 q = 1) (hb : d299930 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d262462, d299930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262462, d299930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77537 q ha hb
  have h2 (q : Pattern) (ha : d262463 q = 1) (hb : d299931 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d262463, d299931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262463, d299931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d262464 q = 1) (hb : d299932 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d262464, d299932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262464, d299932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d262465 q = 1) (hb : d299933 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d262465, d299933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262465, d299933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d262466 q = 1) (hb : d299934 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d262466, d299934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262466, d299934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d262467 q = 1) (hb : d299935 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d262467, d299935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262467, d299935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77539 (p : Pattern) (ha : d262607 p = 1) (hb : d298576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262530 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262539 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d262596 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d262504 q = 1) (hb : d298571 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262504, d298571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77244 q ha hb
    | true =>
      simp only [d262504, d298571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77245 q ha hb
  have h5 (q : Pattern) (ha : d262597 q = 1) (hb : d298572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262597, d298572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d262597, d298572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d262603 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d262604 q = 1) (hb : d298573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262604, d298573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d262604, d298573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d262605 q = 1) (hb : d298574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262605, d298574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262605, d298574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d262606 q = 1) (hb : d298575 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262606, d298575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262606, d298575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d262607 q = 1) (hb : d298576 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262607, d298576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262607, d298576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro77540 (p : Pattern) (ha : d262628 p = 1) (hb : d298586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262530 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262539 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262596 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262504 q = 1) (hb : d298571 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262504, d298571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77244 q ha hb
    | true =>
      simp only [d262504, d298571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77245 q ha hb
  have h4 (q : Pattern) (ha : d262597 q = 1) (hb : d298572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262597, d298572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262597, d298572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d262603 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d262604 q = 1) (hb : d298573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262604, d298573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d262604, d298573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d262605 q = 1) (hb : d298574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262605, d298574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262605, d298574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262606 q = 1) (hb : d298575 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262606, d298575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262606, d298575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d262613 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d262618 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d262620 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d262514 q = 1) (hb : d298581 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262514, d298581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77247 q ha hb
    | true =>
      simp only [d262514, d298581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77248 q ha hb
  have h13 (q : Pattern) (ha : d262621 q = 1) (hb : d298582 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262621, d298582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d262621, d298582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262624 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262625 q = 1) (hb : d298583 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262625, d298583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262625, d298583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262626 q = 1) (hb : d298584 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262626, d298584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d262626, d298584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d262627 q = 1) (hb : d298585 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262627, d298585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d262627, d298585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d262628 q = 1) (hb : d298586 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262628, d298586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d262628, d298586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro77541 (p : Pattern) (ha : d262648 p = 1) (hb : d299939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262620 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262514 q = 1) (hb : d298581 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262514, d298581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77247 q ha hb
    | true =>
      simp only [d262514, d298581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77248 q ha hb
  have h3 (q : Pattern) (ha : d262621 q = 1) (hb : d298582 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262621, d298582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262621, d298582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262624 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262625 q = 1) (hb : d298583 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262625, d298583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262625, d298583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262646 q = 1) (hb : d298584 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262646, d298584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262646, d298584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262647 q = 1) (hb : d298585 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262647, d298585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262647, d298585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262648 q = 1) (hb : d299939 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262648, d299939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262648, d299939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77542 (p : Pattern) (ha : d262733 p = 1) (hb : d299950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262717 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262722 q = 1) (hb : d299945 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262722, d299945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77283 q ha hb
    | true =>
      simp only [d262722, d299945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77286 q ha hb
  have h3 (q : Pattern) (ha : d262723 q = 1) (hb : d299946 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262723, d299946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262723, d299946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262729 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262730 q = 1) (hb : d299947 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262730, d299947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262730, d299947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262731 q = 1) (hb : d299948 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262731, d299948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262731, d299948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262732 q = 1) (hb : d299949 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262732, d299949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262732, d299949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262733 q = 1) (hb : d299950 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262733, d299950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262733, d299950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77543 (p : Pattern) (ha : d262746 p = 1) (hb : d299956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262522 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262629 q = 1) (hb : d298587 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262629, d298587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77539 q ha hb
    | true =>
      simp only [d262629, d298587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77540 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262642 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262643 q = 1) (hb : d298588 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262643, d298588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d262643, d298588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262644 q = 1) (hb : d299937 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262644, d299937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262644, d299937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262645 q = 1) (hb : d299938 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262645, d299938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262645, d299938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262649 q = 1) (hb : d299940 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262649, d299940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262649, d299940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77541 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d262651 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d262652 q = 1) (hb : d299941 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262652, d299941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d262652, d299941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d262653 q = 1) (hb : d299942 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262653, d299942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d262653, d299942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d262654 q = 1) (hb : d299943 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262654, d299943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d262654, d299943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d262655 q = 1) (hb : d299944 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262655, d299944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d262655, d299944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d262734 q = 1) (hb : d299951 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262734, d299951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262734, d299951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77542 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262741 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262742 q = 1) (hb : d299952 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262742, d299952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262742, d299952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262743 q = 1) (hb : d299953 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262743, d299953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d262743, d299953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d262744 q = 1) (hb : d299954 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262744, d299954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d262744, d299954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d262745 q = 1) (hb : d299955 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262745, d299955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d262745, d299955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d262746 q = 1) (hb : d299956 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d262746, d299956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d262746, d299956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro77544 (p : Pattern) (ha : d262752 p = 1) (hb : d299962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262747 q = 1) (hb : d299957 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d262747, d299957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262747, d299957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77543 q ha hb
  have h2 (q : Pattern) (ha : d262748 q = 1) (hb : d299958 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d262748, d299958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262748, d299958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d262749 q = 1) (hb : d299959 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d262749, d299959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262749, d299959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d262750 q = 1) (hb : d299960 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d262750, d299960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262750, d299960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d262751 q = 1) (hb : d299961 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d262751, d299961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262751, d299961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d262752 q = 1) (hb : d299962 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d262752, d299962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262752, d299962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77545 (p : Pattern) (ha : d262965 p = 1) (hb : d298890 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262872 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262881 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d262945 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d262846 q = 1) (hb : d298885 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262846, d298885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77301 q ha hb
    | true =>
      simp only [d262846, d298885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77302 q ha hb
  have h5 (q : Pattern) (ha : d262946 q = 1) (hb : d298886 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262946, d298886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d262946, d298886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d262961 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d262962 q = 1) (hb : d298887 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262962, d298887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d262962, d298887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d262963 q = 1) (hb : d298888 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262963, d298888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262963, d298888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d262964 q = 1) (hb : d298889 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262964, d298889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262964, d298889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d262965 q = 1) (hb : d298890 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262965, d298890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262965, d298890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro77546 (p : Pattern) (ha : d262986 p = 1) (hb : d298900 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262872 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262881 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262945 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262846 q = 1) (hb : d298885 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262846, d298885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77301 q ha hb
    | true =>
      simp only [d262846, d298885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77302 q ha hb
  have h4 (q : Pattern) (ha : d262946 q = 1) (hb : d298886 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262946, d298886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262946, d298886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d262961 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d262962 q = 1) (hb : d298887 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262962, d298887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d262962, d298887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d262963 q = 1) (hb : d298888 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262963, d298888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262963, d298888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262964 q = 1) (hb : d298889 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262964, d298889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262964, d298889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d262971 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d262976 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d262978 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d262856 q = 1) (hb : d298895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262856, d298895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77304 q ha hb
    | true =>
      simp only [d262856, d298895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77305 q ha hb
  have h13 (q : Pattern) (ha : d262979 q = 1) (hb : d298896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262979, d298896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d262979, d298896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262982 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262983 q = 1) (hb : d298897 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262983, d298897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262983, d298897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262984 q = 1) (hb : d298898 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262984, d298898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d262984, d298898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d262985 q = 1) (hb : d298899 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262985, d298899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d262985, d298899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d262986 q = 1) (hb : d298900 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262986, d298900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d262986, d298900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro77547 (p : Pattern) (ha : d263006 p = 1) (hb : d299967 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262856 q = 1) (hb : d298895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262856, d298895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77304 q ha hb
    | true =>
      simp only [d262856, d298895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77305 q ha hb
  have h3 (q : Pattern) (ha : d262979 q = 1) (hb : d298896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262979, d298896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262979, d298896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262982 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262983 q = 1) (hb : d298897 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262983, d298897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262983, d298897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263004 q = 1) (hb : d298898 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263004, d298898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263004, d298898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263005 q = 1) (hb : d298899 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263005, d298899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263005, d298899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263006 q = 1) (hb : d299967 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263006, d299967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263006, d299967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77548 (p : Pattern) (ha : d263127 p = 1) (hb : d299978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263102 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263107 q = 1) (hb : d299973 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263107, d299973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77343 q ha hb
    | true =>
      simp only [d263107, d299973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77348 q ha hb
  have h3 (q : Pattern) (ha : d263108 q = 1) (hb : d299974 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263108, d299974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263108, d299974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263123 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263124 q = 1) (hb : d299975 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263124, d299975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263124, d299975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263125 q = 1) (hb : d299976 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263125, d299976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263125, d299976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263126 q = 1) (hb : d299977 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263126, d299977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263126, d299977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263127 q = 1) (hb : d299978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263127, d299978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263127, d299978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77549 (p : Pattern) (ha : d263140 p = 1) (hb : d299984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262987 q = 1) (hb : d298901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262987, d298901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77545 q ha hb
    | true =>
      simp only [d262987, d298901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77546 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263000 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263001 q = 1) (hb : d298902 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263001, d298902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263001, d298902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263002 q = 1) (hb : d299965 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263002, d299965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263002, d299965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263003 q = 1) (hb : d299966 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263003, d299966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263003, d299966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263007 q = 1) (hb : d299968 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263007, d299968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263007, d299968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77547 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d263009 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d263010 q = 1) (hb : d299969 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263010, d299969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263010, d299969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d263011 q = 1) (hb : d299970 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263011, d299970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263011, d299970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d263012 q = 1) (hb : d299971 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263012, d299971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263012, d299971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d263013 q = 1) (hb : d299972 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263013, d299972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263013, d299972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263128 q = 1) (hb : d299979 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263128, d299979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263128, d299979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77548 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263135 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263136 q = 1) (hb : d299980 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263136, d299980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263136, d299980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d263137 q = 1) (hb : d299981 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263137, d299981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263137, d299981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d263138 q = 1) (hb : d299982 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263138, d299982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263138, d299982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d263139 q = 1) (hb : d299983 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263139, d299983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d263139, d299983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d263140 q = 1) (hb : d299984 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d263140, d299984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263140, d299984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro77550 (p : Pattern) (ha : d263146 p = 1) (hb : d299990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263141 q = 1) (hb : d299985 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d263141, d299985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263141, d299985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77549 q ha hb
  have h2 (q : Pattern) (ha : d263142 q = 1) (hb : d299986 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d263142, d299986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263142, d299986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263143 q = 1) (hb : d299987 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d263143, d299987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263143, d299987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263144 q = 1) (hb : d299988 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d263144, d299988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263144, d299988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263145 q = 1) (hb : d299989 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d263145, d299989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263145, d299989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263146 q = 1) (hb : d299990 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d263146, d299990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263146, d299990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77551 (p : Pattern) (ha : d263364 p = 1) (hb : d299257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263276 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263285 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d263331 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d263250 q = 1) (hb : d299252 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263250, d299252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77364 q ha hb
    | true =>
      simp only [d263250, d299252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77365 q ha hb
  have h5 (q : Pattern) (ha : d263332 q = 1) (hb : d299253 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263332, d299253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d263332, d299253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d263360 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d263361 q = 1) (hb : d299254 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263361, d299254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263361, d299254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d263362 q = 1) (hb : d299255 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263362, d299255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d263362, d299255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263363 q = 1) (hb : d299256 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263363, d299256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263363, d299256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263364 q = 1) (hb : d299257 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263364, d299257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263364, d299257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro77552 (p : Pattern) (ha : d263385 p = 1) (hb : d299267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263276 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263285 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263331 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263250 q = 1) (hb : d299252 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263250, d299252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77364 q ha hb
    | true =>
      simp only [d263250, d299252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77365 q ha hb
  have h4 (q : Pattern) (ha : d263332 q = 1) (hb : d299253 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263332, d299253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d263332, d299253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d263360 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d263361 q = 1) (hb : d299254 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263361, d299254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263361, d299254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d263362 q = 1) (hb : d299255 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263362, d299255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263362, d299255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263363 q = 1) (hb : d299256 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263363, d299256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263363, d299256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d263370 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d263375 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d263377 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d263260 q = 1) (hb : d299262 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263260, d299262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77367 q ha hb
    | true =>
      simp only [d263260, d299262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77368 q ha hb
  have h13 (q : Pattern) (ha : d263378 q = 1) (hb : d299263 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263378, d299263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d263378, d299263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263381 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263382 q = 1) (hb : d299264 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263382, d299264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263382, d299264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d263383 q = 1) (hb : d299265 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263383, d299265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d263383, d299265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d263384 q = 1) (hb : d299266 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263384, d299266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d263384, d299266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d263385 q = 1) (hb : d299267 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263385, d299267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263385, d299267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro77553 (p : Pattern) (ha : d263405 p = 1) (hb : d299996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263377 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263260 q = 1) (hb : d299262 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263260, d299262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77367 q ha hb
    | true =>
      simp only [d263260, d299262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77368 q ha hb
  have h3 (q : Pattern) (ha : d263378 q = 1) (hb : d299263 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263378, d299263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263378, d299263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263381 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263382 q = 1) (hb : d299264 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263382, d299264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263382, d299264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263403 q = 1) (hb : d299265 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263403, d299265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263403, d299265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263404 q = 1) (hb : d299266 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263404, d299266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263404, d299266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263405 q = 1) (hb : d299996 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263405, d299996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263405, d299996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77554 (p : Pattern) (ha : d263537 p = 1) (hb : d300007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263501 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263506 q = 1) (hb : d300002 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263506, d300002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77408 q ha hb
    | true =>
      simp only [d263506, d300002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77414 q ha hb
  have h3 (q : Pattern) (ha : d263507 q = 1) (hb : d300003 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263507, d300003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263507, d300003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263533 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263534 q = 1) (hb : d300004 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263534, d300004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263534, d300004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263535 q = 1) (hb : d300005 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263535, d300005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263535, d300005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263536 q = 1) (hb : d300006 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263536, d300006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263536, d300006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263537 q = 1) (hb : d300007 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263537, d300007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263537, d300007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77555 (p : Pattern) (ha : d263550 p = 1) (hb : d300013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263268 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263386 q = 1) (hb : d299268 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263386, d299268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77551 q ha hb
    | true =>
      simp only [d263386, d299268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77552 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263399 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263400 q = 1) (hb : d299269 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263400, d299269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263400, d299269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263401 q = 1) (hb : d299994 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263401, d299994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263401, d299994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263402 q = 1) (hb : d299995 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263402, d299995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263402, d299995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263406 q = 1) (hb : d299997 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263406, d299997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263406, d299997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77553 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d263408 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d263409 q = 1) (hb : d299998 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263409, d299998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263409, d299998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d263410 q = 1) (hb : d299999 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263410, d299999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263410, d299999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d263411 q = 1) (hb : d300000 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263411, d300000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263411, d300000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d263412 q = 1) (hb : d300001 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263412, d300001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263412, d300001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263538 q = 1) (hb : d300008 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263538, d300008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263538, d300008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77554 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263545 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263546 q = 1) (hb : d300009 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263546, d300009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263546, d300009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d263547 q = 1) (hb : d300010 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263547, d300010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263547, d300010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d263548 q = 1) (hb : d300011 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263548, d300011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263548, d300011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d263549 q = 1) (hb : d300012 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263549, d300012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d263549, d300012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d263550 q = 1) (hb : d300013 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d263550, d300013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263550, d300013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro77556 (p : Pattern) (ha : d263556 p = 1) (hb : d300019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263551 q = 1) (hb : d300014 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d263551, d300014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263551, d300014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77555 q ha hb
  have h2 (q : Pattern) (ha : d263552 q = 1) (hb : d300015 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d263552, d300015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263552, d300015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263553 q = 1) (hb : d300016 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d263553, d300016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263553, d300016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263554 q = 1) (hb : d300017 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d263554, d300017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263554, d300017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263555 q = 1) (hb : d300018 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d263555, d300018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263555, d300018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263556 q = 1) (hb : d300019 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d263556, d300019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263556, d300019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77557 (p : Pattern) (ha : d263768 p = 1) (hb : d299595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263690 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263699 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d263727 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d263664 q = 1) (hb : d299590 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263664, d299590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77432 q ha hb
    | true =>
      simp only [d263664, d299590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77433 q ha hb
  have h5 (q : Pattern) (ha : d263728 q = 1) (hb : d299591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263728, d299591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d263728, d299591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d263764 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d263765 q = 1) (hb : d299592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263765, d299592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263765, d299592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d263766 q = 1) (hb : d299593 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263766, d299593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d263766, d299593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263767 q = 1) (hb : d299594 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263767, d299594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263767, d299594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263768 q = 1) (hb : d299595 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263768, d299595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263768, d299595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro77558 (p : Pattern) (ha : d263790 p = 1) (hb : d299605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263690 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263699 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263727 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263664 q = 1) (hb : d299590 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263664, d299590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77432 q ha hb
    | true =>
      simp only [d263664, d299590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77433 q ha hb
  have h4 (q : Pattern) (ha : d263728 q = 1) (hb : d299591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263728, d299591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d263728, d299591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d263764 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d263765 q = 1) (hb : d299592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263765, d299592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263765, d299592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d263766 q = 1) (hb : d299593 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263766, d299593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263766, d299593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263767 q = 1) (hb : d299594 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263767, d299594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263767, d299594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d263774 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d263779 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d263782 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d263674 q = 1) (hb : d299600 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263674, d299600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77435 q ha hb
    | true =>
      simp only [d263674, d299600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77436 q ha hb
  have h13 (q : Pattern) (ha : d263783 q = 1) (hb : d299601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263783, d299601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d263783, d299601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263786 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263787 q = 1) (hb : d299602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263787, d299602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263787, d299602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d263788 q = 1) (hb : d299603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263788, d299603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d263788, d299603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d263789 q = 1) (hb : d299604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263789, d299604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d263789, d299604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d263790 q = 1) (hb : d299605 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263790, d299605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d263790, d299605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro77559 (p : Pattern) (ha : d263815 p = 1) (hb : d300026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263782 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263674 q = 1) (hb : d299600 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263674, d299600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77435 q ha hb
    | true =>
      simp only [d263674, d299600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77436 q ha hb
  have h3 (q : Pattern) (ha : d263783 q = 1) (hb : d299601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263783, d299601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263783, d299601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263786 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263787 q = 1) (hb : d299602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263787, d299602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263787, d299602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263813 q = 1) (hb : d299603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263813, d299603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263813, d299603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263814 q = 1) (hb : d299604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263814, d299604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263814, d299604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263815 q = 1) (hb : d300026 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263815, d300026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263815, d300026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77560 (p : Pattern) (ha : d263905 p = 1) (hb : d299767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263863 q = 1) (hb : d299752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263863, d299752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77468 q ha hb
    | true =>
      simp only [d263863, d299752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77470 q ha hb
  have h2 (q : Pattern) (ha : d263864 q = 1) (hb : d299753 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263864, d299753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263864, d299753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263865 q = 1) (hb : d299754 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263865, d299754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263865, d299754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263872 q = 1) (hb : d299757 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263872, d299757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77470 q ha hb
    | true =>
      simp only [d263872, d299757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77471 q ha hb
  have h5 (q : Pattern) (ha : d263873 q = 1) (hb : d299758 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263873, d299758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263873, d299758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263874 q = 1) (hb : d299759 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263874, d299759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263874, d299759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263875 q = 1) (hb : d299760 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263875, d299760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263875, d299760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263891 q = 1) (hb : d299757 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263891, d299757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77470 q ha hb
    | true =>
      simp only [d263891, d299757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77475 q ha hb
  have h9 (q : Pattern) (ha : d263892 q = 1) (hb : d299758 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263892, d299758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263892, d299758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263893 q = 1) (hb : d299759 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263893, d299759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263893, d299759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263894 q = 1) (hb : d299765 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263894, d299765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263894, d299765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d263904 q = 1) (hb : d299766 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263904, d299766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263904, d299766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263905 q = 1) (hb : d299767 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263905, d299767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263905, d299767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro77561 (p : Pattern) (ha : d263911 p = 1) (hb : d299781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263906 q = 1) (hb : d299768 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263906, d299768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77560 q ha hb
    | true =>
      simp only [d263906, d299768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263907 q = 1) (hb : d299769 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263907, d299769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263907, d299769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263897 q = 1) (hb : d299776 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263897, d299776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77476 q ha hb
    | true =>
      simp only [d263897, d299776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263898 q = 1) (hb : d299777 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263898, d299777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263898, d299777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263908 q = 1) (hb : d299778 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263908, d299778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263908, d299778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263909 q = 1) (hb : d299779 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263909, d299779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263909, d299779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263910 q = 1) (hb : d299780 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263910, d299780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263910, d299780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d263911 q = 1) (hb : d299781 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263911, d299781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263911, d299781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro77562 (p : Pattern) (ha : d263928 p = 1) (hb : d299756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263857 q = 1) (hb : d299746 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263857, d299746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263857, d299746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77425 q ha hb
  have h2 (q : Pattern) (ha : d263616 q = 1) (hb : d299557 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263616, d299557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77425 q ha hb
    | true =>
      simp only [d263616, d299557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d263858 q = 1) (hb : d299747 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263858, d299747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263858, d299747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263617 q = 1) (hb : d299558 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263617, d299558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263617, d299558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263859 q = 1) (hb : d299748 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263859, d299748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263859, d299748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263860 q = 1) (hb : d299749 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263860, d299749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263860, d299749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d263889 q = 1) (hb : d299755 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263889, d299755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263889, d299755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d15790 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
  have h9 (q : Pattern) (ha : d10412 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d123744 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10412 q = 1) (hb : d263923 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d263923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66730 q ha hb
    | true =>
      simp only [d10412, d263923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10414 q = 1) (hb : d263924 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d263924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10414, d263924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d15792 q = 1) (hb : d263925 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, d263925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15792, d263925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15793 q = 1) (hb : d263926 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, d263926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15793, d263926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d15794 q = 1) (hb : d263927 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15794, d263927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15794, d263927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d263928 q = 1) (hb : d299756 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263928, d299756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263928, d299756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro77563 (p : Pattern) (ha : d263934 p = 1) (hb : d299775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263929 q = 1) (hb : d299757 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263929, d299757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77470 q ha hb
    | true =>
      simp only [d263929, d299757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77562 q ha hb
  have h2 (q : Pattern) (ha : d263930 q = 1) (hb : d299758 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263930, d299758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263930, d299758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263931 q = 1) (hb : d299759 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263931, d299759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263931, d299759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263932 q = 1) (hb : d299765 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263932, d299765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263932, d299765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263933 q = 1) (hb : d299774 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263933, d299774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263933, d299774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263934 q = 1) (hb : d299775 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263934, d299775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263934, d299775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro77564 (p : Pattern) (ha : d263940 p = 1) (hb : d299818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263935 q = 1) (hb : d299776 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263935, d299776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77563 q ha hb
    | true =>
      simp only [d263935, d299776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263936 q = 1) (hb : d299777 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263936, d299777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263936, d299777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263937 q = 1) (hb : d299815 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263937, d299815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263937, d299815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263938 q = 1) (hb : d299816 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263938, d299816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263938, d299816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263939 q = 1) (hb : d299817 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263939, d299817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263939, d299817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263940 q = 1) (hb : d299818 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263940, d299818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263940, d299818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro77565 (p : Pattern) (ha : d263972 p = 1) (hb : d300037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263903 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263941 q = 1) (hb : d300032 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263941, d300032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77561 q ha hb
    | true =>
      simp only [d263941, d300032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77564 q ha hb
  have h3 (q : Pattern) (ha : d263942 q = 1) (hb : d300033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263942, d300033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263942, d300033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263968 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263969 q = 1) (hb : d300034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263969, d300034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263969, d300034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263970 q = 1) (hb : d300035 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263970, d300035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263970, d300035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263971 q = 1) (hb : d300036 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263971, d300036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263971, d300036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263972 q = 1) (hb : d300037 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263972, d300037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263972, d300037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77566 (p : Pattern) (ha : d263989 p = 1) (hb : d300043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263682 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263791 q = 1) (hb : d299606 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263791, d299606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77557 q ha hb
    | true =>
      simp only [d263791, d299606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77558 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263810 q = 1) (hb : d299607 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263810, d299607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263810, d299607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263811 q = 1) (hb : d300024 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263811, d300024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263811, d300024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263812 q = 1) (hb : d300025 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263812, d300025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263812, d300025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263816 q = 1) (hb : d300027 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263816, d300027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263816, d300027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77559 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d263818 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d263819 q = 1) (hb : d300028 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263819, d300028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263819, d300028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d263820 q = 1) (hb : d300029 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263820, d300029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263820, d300029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d263821 q = 1) (hb : d300030 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263821, d300030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263821, d300030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d263822 q = 1) (hb : d300031 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263822, d300031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263822, d300031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263973 q = 1) (hb : d300038 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263973, d300038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263973, d300038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77565 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263984 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263985 q = 1) (hb : d300039 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263985, d300039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263985, d300039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d263986 q = 1) (hb : d300040 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263986, d300040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263986, d300040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d263987 q = 1) (hb : d300041 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263987, d300041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263987, d300041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d263988 q = 1) (hb : d300042 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263988, d300042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d263988, d300042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d263989 q = 1) (hb : d300043 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d263989, d300043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263989, d300043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro77567 (p : Pattern) (ha : d263995 p = 1) (hb : d300049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263990 q = 1) (hb : d300044 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d263990, d300044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263990, d300044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77566 q ha hb
  have h2 (q : Pattern) (ha : d263991 q = 1) (hb : d300045 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d263991, d300045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263991, d300045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263992 q = 1) (hb : d300046 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d263992, d300046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263992, d300046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263993 q = 1) (hb : d300047 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d263993, d300047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263993, d300047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263994 q = 1) (hb : d300048 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d263994, d300048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263994, d300048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263995 q = 1) (hb : d300049 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d263995, d300049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263995, d300049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77568 (p : Pattern) (ha : d264001 p = 1) (hb : d300055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d262468 q = 1) (hb : d299936 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d262468, d299936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77532 q ha hb
    | true =>
      simp only [d262468, d299936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77538 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262753 q = 1) (hb : d299963 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d262753, d299963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262753, d299963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77544 q ha hb
  have h3 (q : Pattern) (ha : d262754 q = 1) (hb : d299964 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d262754, d299964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d262754, d299964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263147 q = 1) (hb : d299991 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d263147, d299991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263147, d299991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77550 q ha hb
  have h5 (q : Pattern) (ha : d263148 q = 1) (hb : d299992 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d263148, d299992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263148, d299992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263149 q = 1) (hb : d299993 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d263149, d299993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263149, d299993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263557 q = 1) (hb : d300020 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d263557, d300020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263557, d300020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77556 q ha hb
  have h8 (q : Pattern) (ha : d263558 q = 1) (hb : d300021 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d263558, d300021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263558, d300021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263559 q = 1) (hb : d300022 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d263559, d300022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263559, d300022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263560 q = 1) (hb : d300023 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d263560, d300023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263560, d300023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263996 q = 1) (hb : d300050 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d263996, d300050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263996, d300050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77567 q ha hb
  have h12 (q : Pattern) (ha : d263997 q = 1) (hb : d300051 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d263997, d300051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263997, d300051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263998 q = 1) (hb : d300052 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d263998, d300052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263998, d300052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263999 q = 1) (hb : d300053 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d263999, d300053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263999, d300053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d264000 q = 1) (hb : d300054 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d264000, d300054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d264000, d300054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d264001 q = 1) (hb : d300055 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d264001, d300055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d264001, d300055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro77569 (p : Pattern) (ha : d264007 p = 1) (hb : d300061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264002 q = 1) (hb : d300056 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d264002, d300056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77568 q ha hb
    | true =>
      simp only [d264002, d300056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264003 q = 1) (hb : d300057 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d264003, d300057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264003, d300057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264004 q = 1) (hb : d300058 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d264004, d300058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264004, d300058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264005 q = 1) (hb : d300059 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d264005, d300059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264005, d300059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264006 q = 1) (hb : d300060 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d264006, d300060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264006, d300060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264007 q = 1) (hb : d300061 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d264007, d300061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264007, d300061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro77570 (p : Pattern) (ha : d264013 p = 1) (hb : d300067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264008 q = 1) (hb : d300062 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d264008, d300062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77569 q ha hb
    | true =>
      simp only [d264008, d300062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264009 q = 1) (hb : d300063 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d264009, d300063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264009, d300063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264010 q = 1) (hb : d300064 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d264010, d300064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264010, d300064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264011 q = 1) (hb : d300065 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d264011, d300065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264011, d300065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264012 q = 1) (hb : d300066 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d264012, d300066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264012, d300066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264013 q = 1) (hb : d300067 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d264013, d300067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264013, d300067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro77571 (p : Pattern) (ha : d264019 p = 1) (hb : d300073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264014 q = 1) (hb : d300068 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d264014, d300068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77570 q ha hb
    | true =>
      simp only [d264014, d300068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264015 q = 1) (hb : d300069 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d264015, d300069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264015, d300069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264016 q = 1) (hb : d300070 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d264016, d300070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264016, d300070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264017 q = 1) (hb : d300071 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d264017, d300071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264017, d300071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264018 q = 1) (hb : d300072 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d264018, d300072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264018, d300072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264019 q = 1) (hb : d300073 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d264019, d300073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264019, d300073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro77572 (p : Pattern) (ha : d264025 p = 1) (hb : d300079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264020 q = 1) (hb : d300074 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d264020, d300074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77571 q ha hb
    | true =>
      simp only [d264020, d300074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264021 q = 1) (hb : d300075 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d264021, d300075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264021, d300075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264022 q = 1) (hb : d300076 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d264022, d300076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264022, d300076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264023 q = 1) (hb : d300077 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d264023, d300077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264023, d300077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264024 q = 1) (hb : d300078 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d264024, d300078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264024, d300078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264025 q = 1) (hb : d300079 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d264025, d300079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264025, d300079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro77573 (p : Pattern) (ha : d264031 p = 1) (hb : d300085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264026 q = 1) (hb : d300080 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d264026, d300080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77572 q ha hb
    | true =>
      simp only [d264026, d300080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264027 q = 1) (hb : d300081 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d264027, d300081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264027, d300081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264028 q = 1) (hb : d300082 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d264028, d300082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264028, d300082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264029 q = 1) (hb : d300083 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d264029, d300083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264029, d300083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264030 q = 1) (hb : d300084 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d264030, d300084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264030, d300084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264031 q = 1) (hb : d300085 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d264031, d300085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264031, d300085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro77574 (p : Pattern) (ha : d264037 p = 1) (hb : d300091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264032 q = 1) (hb : d300086 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d264032, d300086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77573 q ha hb
    | true =>
      simp only [d264032, d300086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264033 q = 1) (hb : d300087 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d264033, d300087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264033, d300087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264034 q = 1) (hb : d300088 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d264034, d300088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264034, d300088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264035 q = 1) (hb : d300089 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d264035, d300089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264035, d300089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264036 q = 1) (hb : d300090 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d264036, d300090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264036, d300090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264037 q = 1) (hb : d300091 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d264037, d300091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264037, d300091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro77575 (p : Pattern) (ha : d264043 p = 1) (hb : d300097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264038 q = 1) (hb : d300092 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d264038, d300092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77574 q ha hb
    | true =>
      simp only [d264038, d300092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264039 q = 1) (hb : d300093 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d264039, d300093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264039, d300093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264040 q = 1) (hb : d300094 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d264040, d300094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264040, d300094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264041 q = 1) (hb : d300095 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d264041, d300095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264041, d300095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264042 q = 1) (hb : d300096 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d264042, d300096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264042, d300096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264043 q = 1) (hb : d300097 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d264043, d300097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264043, d300097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro77576 (p : Pattern) (ha : d265953 p = 1) (hb : d298159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33319 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33325 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d33360 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d298095 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265949 q = 1) (hb : d298155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265949, d298155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d265949, d298155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d33394 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d265950 q = 1) (hb : d298156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265950, d298156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265950, d298156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d265951 q = 1) (hb : d298157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265951, d298157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d265951, d298157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265952 q = 1) (hb : d298158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265952, d298158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265952, d298158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265953 q = 1) (hb : d298159 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265953, d298159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265953, d298159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro77577 (p : Pattern) (ha : d265958 p = 1) (hb : d298166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33319 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33325 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33360 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d298095 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d265949 q = 1) (hb : d298155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265949, d298155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d265949, d298155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d33394 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d265950 q = 1) (hb : d298156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265950, d298156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265950, d298156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d265951 q = 1) (hb : d298157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265951, d298157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265951, d298157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265952 q = 1) (hb : d298158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265952, d298158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d265952, d298158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d33403 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d33407 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d33409 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d298102 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d265954 q = 1) (hb : d298162 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265954, d298162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d265954, d298162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d33415 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d265955 q = 1) (hb : d298163 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265955, d298163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265955, d298163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d265956 q = 1) (hb : d298164 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265956, d298164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d265956, d298164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d265957 q = 1) (hb : d298165 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265957, d298165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d265957, d298165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d265958 q = 1) (hb : d298166 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265958, d298166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265958, d298166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro77578 (p : Pattern) (ha : d265965 p = 1) (hb : d299887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33409 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d298102 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265954 q = 1) (hb : d298162 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265954, d298162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265954, d298162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33415 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265955 q = 1) (hb : d298163 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265955, d298163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265955, d298163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d265963 q = 1) (hb : d298164 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265963, d298164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265963, d298164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265964 q = 1) (hb : d298165 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265964, d298165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265964, d298165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265965 q = 1) (hb : d299887 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265965, d299887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265965, d299887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77579 (p : Pattern) (ha : d265975 p = 1) (hb : d299897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33457 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d298138 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265971 q = 1) (hb : d299893 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265971, d299893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265971, d299893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33483 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265972 q = 1) (hb : d299894 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265972, d299894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265972, d299894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d265973 q = 1) (hb : d299895 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265973, d299895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265973, d299895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265974 q = 1) (hb : d299896 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265974, d299896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265974, d299896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265975 q = 1) (hb : d299897 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265975, d299897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265975, d299897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77580 (p : Pattern) (ha : d265981 p = 1) (hb : d299903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d265959 q = 1) (hb : d298167 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265959, d298167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77576 q ha hb
    | true =>
      simp only [d265959, d298167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77577 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33422 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265960 q = 1) (hb : d298168 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265960, d298168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265960, d298168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265961 q = 1) (hb : d299885 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265961, d299885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265961, d299885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265962 q = 1) (hb : d299886 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265962, d299886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d265962, d299886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265966 q = 1) (hb : d299888 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265966, d299888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265966, d299888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77578 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d265967 q = 1) (hb : d299889 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265967, d299889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d265967, d299889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d265968 q = 1) (hb : d299890 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265968, d299890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265968, d299890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d265969 q = 1) (hb : d299891 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265969, d299891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d265969, d299891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d265970 q = 1) (hb : d299892 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265970, d299892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d265970, d299892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d265976 q = 1) (hb : d299898 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265976, d299898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265976, d299898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77579 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d265977 q = 1) (hb : d299899 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265977, d299899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265977, d299899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d265978 q = 1) (hb : d299900 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265978, d299900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d265978, d299900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d265979 q = 1) (hb : d299901 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265979, d299901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d265979, d299901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d265980 q = 1) (hb : d299902 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265980, d299902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d265980, d299902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d265981 q = 1) (hb : d299903 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d265981, d299903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d265981, d299903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro77581 (p : Pattern) (ha : d265987 p = 1) (hb : d299909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d265944 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d265944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d265944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66749 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d265945 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d265945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d265945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d265946 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d265946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d265946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d265947 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d265947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d265947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d265948 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d265948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d265948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265982 q = 1) (hb : d299904 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d265982, d299904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265982, d299904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77580 q ha hb
  have h8 (q : Pattern) (ha : d265983 q = 1) (hb : d299905 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d265983, d299905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265983, d299905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265984 q = 1) (hb : d299906 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d265984, d299906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265984, d299906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265985 q = 1) (hb : d299907 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d265985, d299907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265985, d299907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d265986 q = 1) (hb : d299908 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d265986, d299908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265986, d299908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d265987 q = 1) (hb : d299909 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d265987, d299909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d265987, d299909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro77582 (p : Pattern) (ha : d265992 p = 1) (hb : d298326 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33543 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33552 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d33602 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d298321 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265988 q = 1) (hb : d298322 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265988, d298322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d265988, d298322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d33653 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d265989 q = 1) (hb : d298323 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265989, d298323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265989, d298323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d265990 q = 1) (hb : d298324 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265990, d298324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d265990, d298324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265991 q = 1) (hb : d298325 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265991, d298325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265991, d298325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265992 q = 1) (hb : d298326 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265992, d298326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265992, d298326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro77583 (p : Pattern) (ha : d265997 p = 1) (hb : d298336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33543 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33552 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33602 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d298321 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d265988 q = 1) (hb : d298322 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265988, d298322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d265988, d298322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d33653 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d265989 q = 1) (hb : d298323 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265989, d298323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265989, d298323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d265990 q = 1) (hb : d298324 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265990, d298324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265990, d298324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265991 q = 1) (hb : d298325 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265991, d298325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d265991, d298325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d33663 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d33668 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d33670 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d298331 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d265993 q = 1) (hb : d298332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265993, d298332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d265993, d298332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d33677 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d265994 q = 1) (hb : d298333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265994, d298333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265994, d298333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d265995 q = 1) (hb : d298334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265995, d298334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d265995, d298334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d265996 q = 1) (hb : d298335 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265996, d298335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d265996, d298335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d265997 q = 1) (hb : d298336 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265997, d298336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265997, d298336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro77584 (p : Pattern) (ha : d266004 p = 1) (hb : d299912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33670 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d298331 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265993 q = 1) (hb : d298332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265993, d298332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265993, d298332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33677 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265994 q = 1) (hb : d298333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265994, d298333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265994, d298333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266002 q = 1) (hb : d298334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266002, d298334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266002, d298334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266003 q = 1) (hb : d298335 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266003, d298335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266003, d298335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266004 q = 1) (hb : d299912 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266004, d299912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266004, d299912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77585 (p : Pattern) (ha : d266014 p = 1) (hb : d299923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d299918 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266010 q = 1) (hb : d299919 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266010, d299919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266010, d299919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33793 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266011 q = 1) (hb : d299920 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266011, d299920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266011, d299920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266012 q = 1) (hb : d299921 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266012, d299921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266012, d299921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266013 q = 1) (hb : d299922 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266013, d299922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266013, d299922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266014 q = 1) (hb : d299923 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266014, d299923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266014, d299923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77586 (p : Pattern) (ha : d266020 p = 1) (hb : d299929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33535 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d265998 q = 1) (hb : d298337 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265998, d298337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77582 q ha hb
    | true =>
      simp only [d265998, d298337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77583 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33695 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265999 q = 1) (hb : d298338 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265999, d298338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265999, d298338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266000 q = 1) (hb : d299910 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266000, d299910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266000, d299910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266001 q = 1) (hb : d299911 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266001, d299911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266001, d299911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266005 q = 1) (hb : d299913 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266005, d299913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266005, d299913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77584 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d33704 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266006 q = 1) (hb : d299914 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266006, d299914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266006, d299914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266007 q = 1) (hb : d299915 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266007, d299915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266007, d299915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266008 q = 1) (hb : d299916 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266008, d299916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266008, d299916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266009 q = 1) (hb : d299917 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266009, d299917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266009, d299917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266015 q = 1) (hb : d299924 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266015, d299924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266015, d299924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77585 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d33809 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266016 q = 1) (hb : d299925 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266016, d299925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266016, d299925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266017 q = 1) (hb : d299926 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266017, d299926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266017, d299926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266018 q = 1) (hb : d299927 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266018, d299927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266018, d299927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266019 q = 1) (hb : d299928 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266019, d299928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266019, d299928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266020 q = 1) (hb : d299929 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266020, d299929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266020, d299929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro77587 (p : Pattern) (ha : d266026 p = 1) (hb : d299935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266021 q = 1) (hb : d299930 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266021, d299930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266021, d299930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77586 q ha hb
  have h2 (q : Pattern) (ha : d266022 q = 1) (hb : d299931 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266022, d299931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266022, d299931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266023 q = 1) (hb : d299932 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266023, d299932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266023, d299932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266024 q = 1) (hb : d299933 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266024, d299933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266024, d299933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266025 q = 1) (hb : d299934 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266025, d299934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266025, d299934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266026 q = 1) (hb : d299935 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266026, d299935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266026, d299935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77588 (p : Pattern) (ha : d266032 p = 1) (hb : d298576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33883 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33892 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d33949 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d298571 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266028 q = 1) (hb : d298572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266028, d298572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d266028, d298572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d34023 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d266029 q = 1) (hb : d298573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266029, d298573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266029, d298573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d266030 q = 1) (hb : d298574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266030, d298574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266030, d298574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266031 q = 1) (hb : d298575 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266031, d298575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266031, d298575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d266032 q = 1) (hb : d298576 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266032, d298576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266032, d298576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro77589 (p : Pattern) (ha : d266037 p = 1) (hb : d298586 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33883 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33892 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33949 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d298571 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d266028 q = 1) (hb : d298572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266028, d298572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266028, d298572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d34023 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d266029 q = 1) (hb : d298573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266029, d298573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266029, d298573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d266030 q = 1) (hb : d298574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266030, d298574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266030, d298574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266031 q = 1) (hb : d298575 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266031, d298575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266031, d298575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d34033 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d34038 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d34040 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d298581 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d266033 q = 1) (hb : d298582 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266033, d298582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d266033, d298582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d34047 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266034 q = 1) (hb : d298583 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266034, d298583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266034, d298583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266035 q = 1) (hb : d298584 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266035, d298584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d266035, d298584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d266036 q = 1) (hb : d298585 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266036, d298585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d266036, d298585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d266037 q = 1) (hb : d298586 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266037, d298586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266037, d298586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro77590 (p : Pattern) (ha : d266044 p = 1) (hb : d299939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34040 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d298581 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266033 q = 1) (hb : d298582 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266033, d298582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266033, d298582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d34047 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266034 q = 1) (hb : d298583 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266034, d298583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266034, d298583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266042 q = 1) (hb : d298584 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266042, d298584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266042, d298584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266043 q = 1) (hb : d298585 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266043, d298585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266043, d298585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266044 q = 1) (hb : d299939 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266044, d299939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266044, d299939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77591 (p : Pattern) (ha : d266054 p = 1) (hb : d299950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34140 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d299945 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266050 q = 1) (hb : d299946 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266050, d299946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266050, d299946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d34195 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266051 q = 1) (hb : d299947 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266051, d299947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266051, d299947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266052 q = 1) (hb : d299948 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266052, d299948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266052, d299948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266053 q = 1) (hb : d299949 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266053, d299949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266053, d299949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266054 q = 1) (hb : d299950 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266054, d299950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266054, d299950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77592 (p : Pattern) (ha : d266060 p = 1) (hb : d299956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266038 q = 1) (hb : d298587 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266038, d298587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77588 q ha hb
    | true =>
      simp only [d266038, d298587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77589 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34065 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266039 q = 1) (hb : d298588 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266039, d298588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266039, d298588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266040 q = 1) (hb : d299937 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266040, d299937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266040, d299937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266041 q = 1) (hb : d299938 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266041, d299938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266041, d299938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266045 q = 1) (hb : d299940 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266045, d299940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266045, d299940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77590 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d34074 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266046 q = 1) (hb : d299941 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266046, d299941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266046, d299941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266047 q = 1) (hb : d299942 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266047, d299942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266047, d299942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266048 q = 1) (hb : d299943 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266048, d299943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266048, d299943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266049 q = 1) (hb : d299944 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266049, d299944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266049, d299944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266055 q = 1) (hb : d299951 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266055, d299951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266055, d299951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77591 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d34211 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266056 q = 1) (hb : d299952 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266056, d299952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266056, d299952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266057 q = 1) (hb : d299953 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266057, d299953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266057, d299953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266058 q = 1) (hb : d299954 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266058, d299954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266058, d299954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266059 q = 1) (hb : d299955 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266059, d299955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266059, d299955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266060 q = 1) (hb : d299956 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266060, d299956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266060, d299956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro77593 (p : Pattern) (ha : d266066 p = 1) (hb : d299962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266061 q = 1) (hb : d299957 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266061, d299957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266061, d299957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77592 q ha hb
  have h2 (q : Pattern) (ha : d266062 q = 1) (hb : d299958 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266062, d299958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266062, d299958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266063 q = 1) (hb : d299959 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266063, d299959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266063, d299959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266064 q = 1) (hb : d299960 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266064, d299960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266064, d299960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266065 q = 1) (hb : d299961 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266065, d299961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266065, d299961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266066 q = 1) (hb : d299962 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266066, d299962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266066, d299962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77594 (p : Pattern) (ha : d266073 p = 1) (hb : d298890 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34342 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d34415 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d298885 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266069 q = 1) (hb : d298886 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266069, d298886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d266069, d298886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d34534 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d266070 q = 1) (hb : d298887 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266070, d298887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266070, d298887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d266071 q = 1) (hb : d298888 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266071, d298888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266071, d298888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266072 q = 1) (hb : d298889 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266072, d298889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266072, d298889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d266073 q = 1) (hb : d298890 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266073, d298890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266073, d298890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro77595 (p : Pattern) (ha : d266078 p = 1) (hb : d298900 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d34342 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34351 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34415 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d298885 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d266069 q = 1) (hb : d298886 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266069, d298886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266069, d298886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d34534 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d266070 q = 1) (hb : d298887 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266070, d298887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266070, d298887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d266071 q = 1) (hb : d298888 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266071, d298888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266071, d298888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266072 q = 1) (hb : d298889 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266072, d298889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266072, d298889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d34544 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d34549 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d34551 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d298895 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d266074 q = 1) (hb : d298896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266074, d298896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d266074, d298896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d34558 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266075 q = 1) (hb : d298897 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266075, d298897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266075, d298897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266076 q = 1) (hb : d298898 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266076, d298898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d266076, d298898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d266077 q = 1) (hb : d298899 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266077, d298899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d266077, d298899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d266078 q = 1) (hb : d298900 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266078, d298900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266078, d298900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro77596 (p : Pattern) (ha : d266085 p = 1) (hb : d299967 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34551 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d298895 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266074 q = 1) (hb : d298896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266074, d298896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266074, d298896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d34558 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266075 q = 1) (hb : d298897 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266075, d298897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266075, d298897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266083 q = 1) (hb : d298898 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266083, d298898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266083, d298898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266084 q = 1) (hb : d298899 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266084, d298899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266084, d298899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266085 q = 1) (hb : d299967 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266085, d299967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266085, d299967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77597 (p : Pattern) (ha : d266095 p = 1) (hb : d299978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34678 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d299973 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266091 q = 1) (hb : d299974 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266091, d299974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266091, d299974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d34751 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266092 q = 1) (hb : d299975 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266092, d299975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266092, d299975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266093 q = 1) (hb : d299976 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266093, d299976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266093, d299976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266094 q = 1) (hb : d299977 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266094, d299977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266094, d299977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266095 q = 1) (hb : d299978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266095, d299978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266095, d299978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77598 (p : Pattern) (ha : d266101 p = 1) (hb : d299984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d34334 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266079 q = 1) (hb : d298901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266079, d298901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77594 q ha hb
    | true =>
      simp only [d266079, d298901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77595 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34576 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266080 q = 1) (hb : d298902 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266080, d298902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266080, d298902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266081 q = 1) (hb : d299965 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266081, d299965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266081, d299965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266082 q = 1) (hb : d299966 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266082, d299966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266082, d299966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266086 q = 1) (hb : d299968 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266086, d299968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266086, d299968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77596 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d34585 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266087 q = 1) (hb : d299969 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266087, d299969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266087, d299969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266088 q = 1) (hb : d299970 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266088, d299970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266088, d299970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266089 q = 1) (hb : d299971 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266089, d299971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266089, d299971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266090 q = 1) (hb : d299972 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266090, d299972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266090, d299972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266096 q = 1) (hb : d299979 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266096, d299979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266096, d299979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77597 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d34767 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266097 q = 1) (hb : d299980 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266097, d299980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266097, d299980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266098 q = 1) (hb : d299981 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266098, d299981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266098, d299981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266099 q = 1) (hb : d299982 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266099, d299982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266099, d299982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266100 q = 1) (hb : d299983 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266100, d299983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266100, d299983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266101 q = 1) (hb : d299984 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266101, d299984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266101, d299984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro77599 (p : Pattern) (ha : d266107 p = 1) (hb : d299990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266102 q = 1) (hb : d299985 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266102, d299985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266102, d299985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77598 q ha hb
  have h2 (q : Pattern) (ha : d266103 q = 1) (hb : d299986 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266103, d299986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266103, d299986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266104 q = 1) (hb : d299987 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266104, d299987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266104, d299987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266105 q = 1) (hb : d299988 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266105, d299988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266105, d299988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266106 q = 1) (hb : d299989 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266106, d299989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266106, d299989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266107 q = 1) (hb : d299990 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266107, d299990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266107, d299990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77600 (p : Pattern) (ha : d266115 p = 1) (hb : d299257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34908 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34917 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d34963 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d299252 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266111 q = 1) (hb : d299253 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266111, d299253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d266111, d299253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d35102 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d266112 q = 1) (hb : d299254 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266112, d299254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266112, d299254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d266113 q = 1) (hb : d299255 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266113, d299255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266113, d299255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266114 q = 1) (hb : d299256 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266114, d299256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266114, d299256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d266115 q = 1) (hb : d299257 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266115, d299257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266115, d299257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro77601 (p : Pattern) (ha : d266120 p = 1) (hb : d299267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d34908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34917 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34963 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d299252 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d266111 q = 1) (hb : d299253 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266111, d299253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266111, d299253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d35102 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d266112 q = 1) (hb : d299254 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266112, d299254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266112, d299254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d266113 q = 1) (hb : d299255 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266113, d299255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266113, d299255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266114 q = 1) (hb : d299256 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266114, d299256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266114, d299256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d35112 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d35117 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d35119 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d299262 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d266116 q = 1) (hb : d299263 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266116, d299263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d266116, d299263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d35126 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266117 q = 1) (hb : d299264 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266117, d299264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266117, d299264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266118 q = 1) (hb : d299265 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266118, d299265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d266118, d299265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d266119 q = 1) (hb : d299266 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266119, d299266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d266119, d299266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d266120 q = 1) (hb : d299267 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266120, d299267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266120, d299267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro77602 (p : Pattern) (ha : d266127 p = 1) (hb : d299996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35119 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d299262 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266116 q = 1) (hb : d299263 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266116, d299263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266116, d299263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d35126 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266117 q = 1) (hb : d299264 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266117, d299264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266117, d299264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266125 q = 1) (hb : d299265 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266125, d299265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266125, d299265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266126 q = 1) (hb : d299266 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266126, d299266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266126, d299266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266127 q = 1) (hb : d299996 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266127, d299996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266127, d299996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77603 (p : Pattern) (ha : d266137 p = 1) (hb : d300007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35246 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d300002 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266133 q = 1) (hb : d300003 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266133, d300003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266133, d300003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d35330 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266134 q = 1) (hb : d300004 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266134, d300004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266134, d300004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266135 q = 1) (hb : d300005 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266135, d300005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266135, d300005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266136 q = 1) (hb : d300006 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266136, d300006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266136, d300006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266137 q = 1) (hb : d300007 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266137, d300007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266137, d300007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77604 (p : Pattern) (ha : d266143 p = 1) (hb : d300013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d34900 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266121 q = 1) (hb : d299268 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266121, d299268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77600 q ha hb
    | true =>
      simp only [d266121, d299268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77601 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d35144 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266122 q = 1) (hb : d299269 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266122, d299269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266122, d299269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266123 q = 1) (hb : d299994 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266123, d299994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266123, d299994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266124 q = 1) (hb : d299995 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266124, d299995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266124, d299995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266128 q = 1) (hb : d299997 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266128, d299997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266128, d299997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77602 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d35153 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266129 q = 1) (hb : d299998 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266129, d299998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266129, d299998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266130 q = 1) (hb : d299999 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266130, d299999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266130, d299999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266131 q = 1) (hb : d300000 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266131, d300000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266131, d300000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266132 q = 1) (hb : d300001 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266132, d300001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266132, d300001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266138 q = 1) (hb : d300008 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266138, d300008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266138, d300008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77603 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d35346 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266139 q = 1) (hb : d300009 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266139, d300009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266139, d300009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266140 q = 1) (hb : d300010 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266140, d300010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266140, d300010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266141 q = 1) (hb : d300011 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266141, d300011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266141, d300011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266142 q = 1) (hb : d300012 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266142, d300012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266142, d300012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266143 q = 1) (hb : d300013 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266143, d300013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266143, d300013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro77605 (p : Pattern) (ha : d266149 p = 1) (hb : d300019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266144 q = 1) (hb : d300014 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266144, d300014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266144, d300014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77604 q ha hb
  have h2 (q : Pattern) (ha : d266145 q = 1) (hb : d300015 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266145, d300015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266145, d300015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266146 q = 1) (hb : d300016 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266146, d300016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266146, d300016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266147 q = 1) (hb : d300017 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266147, d300017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266147, d300017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266148 q = 1) (hb : d300018 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266148, d300018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266148, d300018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266149 q = 1) (hb : d300019 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266149, d300019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266149, d300019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77606 (p : Pattern) (ha : d266158 p = 1) (hb : d299595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35491 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d35500 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d35528 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d299590 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266154 q = 1) (hb : d299591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266154, d299591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d266154, d299591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d35669 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d266155 q = 1) (hb : d299592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266155, d299592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266155, d299592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d266156 q = 1) (hb : d299593 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266156, d299593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266156, d299593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266157 q = 1) (hb : d299594 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266157, d299594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266157, d299594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d266158 q = 1) (hb : d299595 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266158, d299595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266158, d299595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro77607 (p : Pattern) (ha : d266163 p = 1) (hb : d299605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d35491 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35500 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d35528 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d299590 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d266154 q = 1) (hb : d299591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266154, d299591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266154, d299591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d35669 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d266155 q = 1) (hb : d299592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266155, d299592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266155, d299592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d266156 q = 1) (hb : d299593 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266156, d299593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266156, d299593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266157 q = 1) (hb : d299594 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266157, d299594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266157, d299594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d35679 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d35684 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d35687 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d299600 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d266159 q = 1) (hb : d299601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266159, d299601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d266159, d299601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d35694 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266160 q = 1) (hb : d299602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266160, d299602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266160, d299602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266161 q = 1) (hb : d299603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266161, d299603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d266161, d299603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d266162 q = 1) (hb : d299604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266162, d299604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d266162, d299604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d266163 q = 1) (hb : d299605 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266163, d299605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266163, d299605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro77608 (p : Pattern) (ha : d266170 p = 1) (hb : d300026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35687 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d299600 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266159 q = 1) (hb : d299601 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266159, d299601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266159, d299601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d35694 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266160 q = 1) (hb : d299602 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266160, d299602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266160, d299602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266168 q = 1) (hb : d299603 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266168, d299603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266168, d299603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266169 q = 1) (hb : d299604 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266169, d299604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266169, d299604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266170 q = 1) (hb : d300026 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266170, d300026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266170, d300026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77609 (p : Pattern) (ha : d266180 p = 1) (hb : d300037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35811 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d300032 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266176 q = 1) (hb : d300033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266176, d300033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266176, d300033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d35929 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266177 q = 1) (hb : d300034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266177, d300034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266177, d300034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266178 q = 1) (hb : d300035 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266178, d300035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266178, d300035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266179 q = 1) (hb : d300036 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266179, d300036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266179, d300036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266180 q = 1) (hb : d300037 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266180, d300037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266180, d300037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77610 (p : Pattern) (ha : d266186 p = 1) (hb : d300043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d35483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266164 q = 1) (hb : d299606 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266164, d299606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77606 q ha hb
    | true =>
      simp only [d266164, d299606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77607 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d35717 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266165 q = 1) (hb : d299607 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266165, d299607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266165, d299607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266166 q = 1) (hb : d300024 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266166, d300024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266166, d300024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266167 q = 1) (hb : d300025 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266167, d300025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266167, d300025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266171 q = 1) (hb : d300027 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266171, d300027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266171, d300027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77608 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d35726 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266172 q = 1) (hb : d300028 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266172, d300028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266172, d300028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266173 q = 1) (hb : d300029 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266173, d300029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266173, d300029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266174 q = 1) (hb : d300030 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266174, d300030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266174, d300030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266175 q = 1) (hb : d300031 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266175, d300031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266175, d300031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266181 q = 1) (hb : d300038 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266181, d300038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266181, d300038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77609 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d35945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266182 q = 1) (hb : d300039 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266182, d300039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266182, d300039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266183 q = 1) (hb : d300040 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266183, d300040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266183, d300040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266184 q = 1) (hb : d300041 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266184, d300041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266184, d300041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266185 q = 1) (hb : d300042 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266185, d300042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266185, d300042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266186 q = 1) (hb : d300043 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266186, d300043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266186, d300043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro77611 (p : Pattern) (ha : d266192 p = 1) (hb : d300049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266187 q = 1) (hb : d300044 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266187, d300044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266187, d300044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77610 q ha hb
  have h2 (q : Pattern) (ha : d266188 q = 1) (hb : d300045 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266188, d300045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266188, d300045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266189 q = 1) (hb : d300046 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266189, d300046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266189, d300046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266190 q = 1) (hb : d300047 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266190, d300047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266190, d300047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266191 q = 1) (hb : d300048 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266191, d300048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266191, d300048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266192 q = 1) (hb : d300049 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266192, d300049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266192, d300049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77612 (p : Pattern) (ha : d266198 p = 1) (hb : d300055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d266027 q = 1) (hb : d299936 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266027, d299936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77581 q ha hb
    | true =>
      simp only [d266027, d299936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77587 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d266067 q = 1) (hb : d299963 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266067, d299963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266067, d299963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77593 q ha hb
  have h3 (q : Pattern) (ha : d266068 q = 1) (hb : d299964 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d266068, d299964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266068, d299964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266108 q = 1) (hb : d299991 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266108, d299991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266108, d299991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77599 q ha hb
  have h5 (q : Pattern) (ha : d266109 q = 1) (hb : d299992 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d266109, d299992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266109, d299992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266110 q = 1) (hb : d299993 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d266110, d299993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266110, d299993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266150 q = 1) (hb : d300020 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266150, d300020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266150, d300020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77605 q ha hb
  have h8 (q : Pattern) (ha : d266151 q = 1) (hb : d300021 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d266151, d300021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266151, d300021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266152 q = 1) (hb : d300022 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d266152, d300022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266152, d300022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d266153 q = 1) (hb : d300023 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d266153, d300023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266153, d300023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d266193 q = 1) (hb : d300050 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266193, d300050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266193, d300050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77611 q ha hb
  have h12 (q : Pattern) (ha : d266194 q = 1) (hb : d300051 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d266194, d300051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266194, d300051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266195 q = 1) (hb : d300052 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d266195, d300052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266195, d300052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d266196 q = 1) (hb : d300053 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d266196, d300053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266196, d300053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d266197 q = 1) (hb : d300054 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d266197, d300054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266197, d300054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d266198 q = 1) (hb : d300055 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d266198, d300055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266198, d300055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro77613 (p : Pattern) (ha : d266204 p = 1) (hb : d300061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266199 q = 1) (hb : d300056 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d266199, d300056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77612 q ha hb
    | true =>
      simp only [d266199, d300056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266200 q = 1) (hb : d300057 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d266200, d300057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266200, d300057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266201 q = 1) (hb : d300058 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d266201, d300058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266201, d300058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266202 q = 1) (hb : d300059 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d266202, d300059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266202, d300059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266203 q = 1) (hb : d300060 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d266203, d300060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266203, d300060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266204 q = 1) (hb : d300061 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d266204, d300061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266204, d300061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77614 (p : Pattern) (ha : d266210 p = 1) (hb : d300067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266205 q = 1) (hb : d300062 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d266205, d300062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77613 q ha hb
    | true =>
      simp only [d266205, d300062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266206 q = 1) (hb : d300063 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d266206, d300063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266206, d300063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266207 q = 1) (hb : d300064 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d266207, d300064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266207, d300064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266208 q = 1) (hb : d300065 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d266208, d300065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266208, d300065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266209 q = 1) (hb : d300066 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d266209, d300066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266209, d300066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266210 q = 1) (hb : d300067 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d266210, d300067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266210, d300067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77615 (p : Pattern) (ha : d266216 p = 1) (hb : d300073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266211 q = 1) (hb : d300068 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d266211, d300068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77614 q ha hb
    | true =>
      simp only [d266211, d300068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266212 q = 1) (hb : d300069 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d266212, d300069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266212, d300069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266213 q = 1) (hb : d300070 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d266213, d300070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266213, d300070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266214 q = 1) (hb : d300071 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d266214, d300071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266214, d300071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266215 q = 1) (hb : d300072 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d266215, d300072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266215, d300072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266216 q = 1) (hb : d300073 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d266216, d300073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266216, d300073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77616 (p : Pattern) (ha : d266222 p = 1) (hb : d300079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266217 q = 1) (hb : d300074 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d266217, d300074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77615 q ha hb
    | true =>
      simp only [d266217, d300074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266218 q = 1) (hb : d300075 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d266218, d300075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266218, d300075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266219 q = 1) (hb : d300076 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d266219, d300076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266219, d300076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266220 q = 1) (hb : d300077 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d266220, d300077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266220, d300077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266221 q = 1) (hb : d300078 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d266221, d300078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266221, d300078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266222 q = 1) (hb : d300079 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d266222, d300079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266222, d300079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77617 (p : Pattern) (ha : d266228 p = 1) (hb : d300085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266223 q = 1) (hb : d300080 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d266223, d300080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77616 q ha hb
    | true =>
      simp only [d266223, d300080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266224 q = 1) (hb : d300081 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d266224, d300081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266224, d300081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266225 q = 1) (hb : d300082 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d266225, d300082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266225, d300082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266226 q = 1) (hb : d300083 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d266226, d300083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266226, d300083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266227 q = 1) (hb : d300084 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d266227, d300084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266227, d300084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266228 q = 1) (hb : d300085 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d266228, d300085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266228, d300085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77618 (p : Pattern) (ha : d266234 p = 1) (hb : d300091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266229 q = 1) (hb : d300086 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d266229, d300086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77617 q ha hb
    | true =>
      simp only [d266229, d300086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266230 q = 1) (hb : d300087 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d266230, d300087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266230, d300087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266231 q = 1) (hb : d300088 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d266231, d300088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266231, d300088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266232 q = 1) (hb : d300089 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d266232, d300089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266232, d300089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266233 q = 1) (hb : d300090 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d266233, d300090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266233, d300090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266234 q = 1) (hb : d300091 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d266234, d300091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266234, d300091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77619 (p : Pattern) (ha : d266240 p = 1) (hb : d300097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266235 q = 1) (hb : d300092 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d266235, d300092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77618 q ha hb
    | true =>
      simp only [d266235, d300092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266236 q = 1) (hb : d300093 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d266236, d300093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266236, d300093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266237 q = 1) (hb : d300094 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d266237, d300094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266237, d300094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266238 q = 1) (hb : d300095 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d266238, d300095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266238, d300095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266239 q = 1) (hb : d300096 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d266239, d300096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266239, d300096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266240 q = 1) (hb : d300097 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d266240, d300097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266240, d300097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77620 (p : Pattern) (ha : d18 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17 q = 1) (hb : d300099 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d17, d300099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d17, d300099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d18, d300100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18, d300100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro77621 (p : Pattern) (ha : d24 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77620 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d24, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77622 (p : Pattern) (ha : d30 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77621 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77623 (p : Pattern) (ha : d36 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77622 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d34 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d35 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77624 (p : Pattern) (ha : d42 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77623 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77625 (p : Pattern) (ha : d48 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77624 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d48 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77626 (p : Pattern) (ha : d49 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77623 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d49 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77627 (p : Pattern) (ha : d55 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77624 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77626 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d55 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro77628 (p : Pattern) (ha : d60 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77626 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d52 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77629 (p : Pattern) (ha : d71 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d66 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77621 q ha hb
  have h2 (q : Pattern) (ha : d25 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77621 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d68 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d70 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d71 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d71, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d71, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro77630 (p : Pattern) (ha : d77 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77629 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d73 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77631 (p : Pattern) (ha : d83 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77630 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d79 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d81 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77632 (p : Pattern) (ha : d89 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77631 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d86 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d87 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77633 (p : Pattern) (ha : d95 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77625 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77627 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77628 q ha hb
  have h6 (q : Pattern) (ha : d62 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d63 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d64 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d65 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d90 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77632 q ha hb
  have h11 (q : Pattern) (ha : d91 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d92 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d93 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d95 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d95, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d95, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro77634 (p : Pattern) (ha : d104 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77624 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d104 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77635 (p : Pattern) (ha : d111 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77624 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77626 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d107 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d110 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d111 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro77636 (p : Pattern) (ha : d213 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77624 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d213 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77637 (p : Pattern) (ha : d116 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77623 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77638 (p : Pattern) (ha : d123 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77623 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77639 (p : Pattern) (ha : d25432 p = 1) (hb : d300100 p = 1) : d304072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16 q = 1) (hb : d216468 q = 1) : d16 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131 q = 1) (hb : d300099 q = 1) : d304071 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d131, d300099, d304071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131, d300099, d304071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25432 q = 1) (hb : d300100 q = 1) : d304072 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d25432, d300100, d304072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25432, d300100, d304072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro77640 (p : Pattern) (ha : d30638 p = 1) (hb : d300100 p = 1) : d304078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25433 q = 1) (hb : d300100 q = 1) : d304073 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d304073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77639 q ha hb
    | true =>
      simp only [d25433, d304073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25434 q = 1) (hb : d300100 q = 1) : d304074 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d304074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25434, d304074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77620 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30635 q = 1) (hb : d300100 q = 1) : d304075 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30635, d304075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30635, d304075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30636 q = 1) (hb : d300100 q = 1) : d304076 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30636, d304076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30636, d304076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30637 q = 1) (hb : d300100 q = 1) : d304077 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30637, d304077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30637, d304077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30638 q = 1) (hb : d300100 q = 1) : d304078 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30638, d304078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30638, d304078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro77641 (p : Pattern) (ha : d30644 p = 1) (hb : d300100 p = 1) : d304084 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30639 q = 1) (hb : d300100 q = 1) : d304079 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30639, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77640 q ha hb
    | true =>
      simp only [d30639, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30640 q = 1) (hb : d300100 q = 1) : d304080 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30640, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30640, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30641 q = 1) (hb : d300100 q = 1) : d304081 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30641, d304081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30641, d304081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30642 q = 1) (hb : d300100 q = 1) : d304082 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30642, d304082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30642, d304082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77621 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30643 q = 1) (hb : d300100 q = 1) : d304083 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30643, d304083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30643, d304083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30644 q = 1) (hb : d300100 q = 1) : d304084 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30644, d304084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30644, d304084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro77642 (p : Pattern) (ha : d30650 p = 1) (hb : d300100 p = 1) : d304090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30645 q = 1) (hb : d300100 q = 1) : d304085 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30645, d304085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77641 q ha hb
    | true =>
      simp only [d30645, d304085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77622 q ha hb
  have h2 (q : Pattern) (ha : d30646 q = 1) (hb : d300100 q = 1) : d304086 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30646, d304086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30646, d304086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30647 q = 1) (hb : d300100 q = 1) : d304087 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30647, d304087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30647, d304087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77622 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30648 q = 1) (hb : d300100 q = 1) : d304088 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30648, d304088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30648, d304088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30649 q = 1) (hb : d300100 q = 1) : d304089 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d30649, d304089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30649, d304089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30650 q = 1) (hb : d300100 q = 1) : d304090 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d30650, d304090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30650, d304090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro77643 (p : Pattern) (ha : d30656 p = 1) (hb : d300100 p = 1) : d304096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d300100 q = 1) : d304091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77642 q ha hb
    | true =>
      simp only [d30651, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d300100 q = 1) : d304092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77623 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30653 q = 1) (hb : d300100 q = 1) : d304093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30653, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30653, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30654 q = 1) (hb : d300100 q = 1) : d304094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30654, d304094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30654, d304094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30655 q = 1) (hb : d300100 q = 1) : d304095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30655, d304095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30655, d304095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30656 q = 1) (hb : d300100 q = 1) : d304096 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30656, d304096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30656, d304096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77644 (p : Pattern) (ha : d245354 p = 1) (hb : d300100 p = 1) : d304102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77637 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77638 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30657 q = 1) (hb : d300100 q = 1) : d304097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30657, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77643 q ha hb
    | true =>
      simp only [d30657, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77624 q ha hb
  have h9 (q : Pattern) (ha : d245350 q = 1) (hb : d300100 q = 1) : d304098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245350, d304098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245350, d304098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77624 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245351 q = 1) (hb : d300100 q = 1) : d304099 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245351, d304099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245351, d304099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245352 q = 1) (hb : d300100 q = 1) : d304100 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245352, d304100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245352, d304100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245353 q = 1) (hb : d300100 q = 1) : d304101 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245353, d304101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245353, d304101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d245354 q = 1) (hb : d300100 q = 1) : d304102 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245354, d304102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245354, d304102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro77645 (p : Pattern) (ha : d194 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77623 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77646 (p : Pattern) (ha : d199 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77623 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d199 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77647 (p : Pattern) (ha : d30663 p = 1) (hb : d300100 p = 1) : d304103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d300100 q = 1) : d304091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77642 q ha hb
    | true =>
      simp only [d30651, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d300100 q = 1) : d304092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77623 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30653 q = 1) (hb : d300100 q = 1) : d304093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30653, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30653, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30654 q = 1) (hb : d300100 q = 1) : d304094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30654, d304094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30654, d304094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30655 q = 1) (hb : d300100 q = 1) : d304095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30655, d304095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30655, d304095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30663 q = 1) (hb : d300100 q = 1) : d304103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30663, d304103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30663, d304103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro77648 (p : Pattern) (ha : d245359 p = 1) (hb : d300100 p = 1) : d304109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77637 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77638 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30657 q = 1) (hb : d300100 q = 1) : d304097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30657, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77643 q ha hb
    | true =>
      simp only [d30657, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77624 q ha hb
  have h9 (q : Pattern) (ha : d245350 q = 1) (hb : d300100 q = 1) : d304098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245350, d304098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245350, d304098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77624 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245351 q = 1) (hb : d300100 q = 1) : d304099 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245351, d304099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245351, d304099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245352 q = 1) (hb : d300100 q = 1) : d304100 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245352, d304100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245352, d304100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245353 q = 1) (hb : d300100 q = 1) : d304101 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245353, d304101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245353, d304101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77645 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77646 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d30664 q = 1) (hb : d300100 q = 1) : d304104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30664, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77647 q ha hb
    | true =>
      simp only [d30664, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77626 q ha hb
  have h23 (q : Pattern) (ha : d245355 q = 1) (hb : d300100 q = 1) : d304105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245355, d304105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d245355, d304105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77626 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d245356 q = 1) (hb : d300100 q = 1) : d304106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245356, d304106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d245356, d304106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d245357 q = 1) (hb : d300100 q = 1) : d304107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245357, d304107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d245357, d304107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d245358 q = 1) (hb : d300100 q = 1) : d304108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245358, d304108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d245358, d304108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d245359 q = 1) (hb : d300100 q = 1) : d304109 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245359, d304109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245359, d304109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro77649 (p : Pattern) (ha : d245366 p = 1) (hb : d300100 p = 1) : d304114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30664 q = 1) (hb : d300100 q = 1) : d304104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30664, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77647 q ha hb
    | true =>
      simp only [d30664, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77626 q ha hb
  have h2 (q : Pattern) (ha : d245355 q = 1) (hb : d300100 q = 1) : d304105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245355, d304105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245355, d304105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77626 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245356 q = 1) (hb : d300100 q = 1) : d304106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245356, d304106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245356, d304106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245364 q = 1) (hb : d300100 q = 1) : d304107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245364, d304107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245364, d304107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245365 q = 1) (hb : d300100 q = 1) : d304108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245365, d304108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245365, d304108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245366 q = 1) (hb : d300100 q = 1) : d304114 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245366, d304114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245366, d304114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77650 (p : Pattern) (ha : d30687 p = 1) (hb : d300100 p = 1) : d304125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30682 q = 1) (hb : d300100 q = 1) : d304120 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30682, d304120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30682, d304120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77640 q ha hb
  have h2 (q : Pattern) (ha : d30639 q = 1) (hb : d300100 q = 1) : d304079 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30639, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77640 q ha hb
    | true =>
      simp only [d30639, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30683 q = 1) (hb : d300100 q = 1) : d304121 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30683, d304121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30683, d304121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30640 q = 1) (hb : d300100 q = 1) : d304080 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30640, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30640, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30684 q = 1) (hb : d300100 q = 1) : d304122 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30684, d304122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30684, d304122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30685 q = 1) (hb : d300100 q = 1) : d304123 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30685, d304123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30685, d304123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77621 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77621 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30686 q = 1) (hb : d300100 q = 1) : d304124 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30686, d304124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30686, d304124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d30687 q = 1) (hb : d300100 q = 1) : d304125 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30687, d304125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d30687, d304125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro77651 (p : Pattern) (ha : d30693 p = 1) (hb : d300100 p = 1) : d304131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30688 q = 1) (hb : d300100 q = 1) : d304126 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30688, d304126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77650 q ha hb
    | true =>
      simp only [d30688, d304126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77629 q ha hb
  have h2 (q : Pattern) (ha : d30689 q = 1) (hb : d300100 q = 1) : d304127 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30689, d304127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30689, d304127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30690 q = 1) (hb : d300100 q = 1) : d304128 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30690, d304128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30690, d304128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77629 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30691 q = 1) (hb : d300100 q = 1) : d304129 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30691, d304129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30691, d304129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30692 q = 1) (hb : d300100 q = 1) : d304130 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d30692, d304130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30692, d304130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30693 q = 1) (hb : d300100 q = 1) : d304131 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d30693, d304131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30693, d304131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro77652 (p : Pattern) (ha : d30699 p = 1) (hb : d300100 p = 1) : d304137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30694 q = 1) (hb : d300100 q = 1) : d304132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30694, d304132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77651 q ha hb
    | true =>
      simp only [d30694, d304132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30695 q = 1) (hb : d300100 q = 1) : d304133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30695, d304133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30695, d304133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77630 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30696 q = 1) (hb : d300100 q = 1) : d304134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30696, d304134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30696, d304134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30697 q = 1) (hb : d300100 q = 1) : d304135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30697, d304135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30697, d304135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30698 q = 1) (hb : d300100 q = 1) : d304136 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30698, d304136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30698, d304136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30699 q = 1) (hb : d300100 q = 1) : d304137 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30699, d304137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30699, d304137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro77653 (p : Pattern) (ha : d245376 p = 1) (hb : d300100 p = 1) : d304143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30700 q = 1) (hb : d300100 q = 1) : d304138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30700, d304138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77652 q ha hb
    | true =>
      simp only [d30700, d304138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77631 q ha hb
  have h2 (q : Pattern) (ha : d245372 q = 1) (hb : d300100 q = 1) : d304139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245372, d304139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245372, d304139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77631 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245373 q = 1) (hb : d300100 q = 1) : d304140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245373, d304140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245373, d304140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245374 q = 1) (hb : d300100 q = 1) : d304141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245374, d304141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245374, d304141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245375 q = 1) (hb : d300100 q = 1) : d304142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245375, d304142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245375, d304142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245376 q = 1) (hb : d300100 q = 1) : d304143 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245376, d304143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245376, d304143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77654 (p : Pattern) (ha : d245382 p = 1) (hb : d300100 p = 1) : d304149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77634 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77634 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77635 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245360 q = 1) (hb : d300100 q = 1) : d304110 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245360, d304110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77644 q ha hb
    | true =>
      simp only [d245360, d304110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77648 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77636 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d245361 q = 1) (hb : d300100 q = 1) : d304111 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245361, d304111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245361, d304111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245362 q = 1) (hb : d300100 q = 1) : d304112 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245362, d304112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245362, d304112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d245363 q = 1) (hb : d300100 q = 1) : d304113 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245363, d304113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245363, d304113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245367 q = 1) (hb : d300100 q = 1) : d304115 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245367, d304115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245367, d304115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77649 q ha hb
  have h12 (q : Pattern) (ha : d245368 q = 1) (hb : d300100 q = 1) : d304116 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245368, d304116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245368, d304116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d245369 q = 1) (hb : d300100 q = 1) : d304117 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245369, d304117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245369, d304117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d245370 q = 1) (hb : d300100 q = 1) : d304118 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245370, d304118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245370, d304118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245371 q = 1) (hb : d300100 q = 1) : d304119 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245371, d304119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245371, d304119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d245377 q = 1) (hb : d300100 q = 1) : d304144 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245377, d304144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245377, d304144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77653 q ha hb
  have h17 (q : Pattern) (ha : d245378 q = 1) (hb : d300100 q = 1) : d304145 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245378, d304145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245378, d304145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d245379 q = 1) (hb : d300100 q = 1) : d304146 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245379, d304146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245379, d304146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d245380 q = 1) (hb : d300100 q = 1) : d304147 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245380, d304147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d245380, d304147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d245381 q = 1) (hb : d300100 q = 1) : d304148 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245381, d304148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d245381, d304148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d245382 q = 1) (hb : d300100 q = 1) : d304149 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245382, d304149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245382, d304149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro77655 (p : Pattern) (ha : d406 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77626 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d107 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d110 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d406 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77656 (p : Pattern) (ha : d462 p = 1) (hb : d300100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77631 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d458 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d459 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d460 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d461 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d462 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77657 (p : Pattern) (ha : d30721 p = 1) (hb : d300100 p = 1) : d304159 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30657 q = 1) (hb : d300100 q = 1) : d304097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30657, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77643 q ha hb
    | true =>
      simp only [d30657, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77624 q ha hb
  have h2 (q : Pattern) (ha : d30717 q = 1) (hb : d300100 q = 1) : d304155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30717, d304155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30717, d304155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30718 q = 1) (hb : d300100 q = 1) : d304156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30718, d304156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30718, d304156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30719 q = 1) (hb : d300100 q = 1) : d304157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30719, d304157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30719, d304157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30720 q = 1) (hb : d300100 q = 1) : d304158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30720, d304158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30720, d304158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30721 q = 1) (hb : d300100 q = 1) : d304159 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d30721, d304159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30721, d304159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77658 (p : Pattern) (ha : d30728 p = 1) (hb : d300100 p = 1) : d304166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30657 q = 1) (hb : d300100 q = 1) : d304097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30657, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77643 q ha hb
    | true =>
      simp only [d30657, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77624 q ha hb
  have h2 (q : Pattern) (ha : d30717 q = 1) (hb : d300100 q = 1) : d304155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30717, d304155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30717, d304155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30718 q = 1) (hb : d300100 q = 1) : d304156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30718, d304156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30718, d304156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30719 q = 1) (hb : d300100 q = 1) : d304157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30719, d304157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30719, d304157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30720 q = 1) (hb : d300100 q = 1) : d304158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30720, d304158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30720, d304158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30664 q = 1) (hb : d300100 q = 1) : d304104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30664, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77647 q ha hb
    | true =>
      simp only [d30664, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77626 q ha hb
  have h7 (q : Pattern) (ha : d30724 q = 1) (hb : d300100 q = 1) : d304162 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30724, d304162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30724, d304162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30725 q = 1) (hb : d300100 q = 1) : d304163 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30725, d304163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30725, d304163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30726 q = 1) (hb : d300100 q = 1) : d304164 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30726, d304164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30726, d304164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30727 q = 1) (hb : d300100 q = 1) : d304165 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30727, d304165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30727, d304165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30728 q = 1) (hb : d300100 q = 1) : d304166 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d30728, d304166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30728, d304166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro77659 (p : Pattern) (ha : d30834 p = 1) (hb : d300100 p = 1) : d304231 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30657 q = 1) (hb : d300100 q = 1) : d304097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30657, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77643 q ha hb
    | true =>
      simp only [d30657, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77624 q ha hb
  have h2 (q : Pattern) (ha : d30717 q = 1) (hb : d300100 q = 1) : d304155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30717, d304155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30717, d304155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30718 q = 1) (hb : d300100 q = 1) : d304156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30718, d304156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30718, d304156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30719 q = 1) (hb : d300100 q = 1) : d304157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30719, d304157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30719, d304157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30720 q = 1) (hb : d300100 q = 1) : d304158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30720, d304158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30720, d304158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77624 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30834 q = 1) (hb : d300100 q = 1) : d304231 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d30834, d304231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30834, d304231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro77660 (p : Pattern) (ha : d30733 p = 1) (hb : d300100 p = 1) : d304171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d300100 q = 1) : d304091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77642 q ha hb
    | true =>
      simp only [d30651, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d300100 q = 1) : d304092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77623 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30653 q = 1) (hb : d300100 q = 1) : d304093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30653, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30653, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30654 q = 1) (hb : d300100 q = 1) : d304094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30654, d304094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30654, d304094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30732 q = 1) (hb : d300100 q = 1) : d304170 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30732, d304170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30732, d304170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30733 q = 1) (hb : d300100 q = 1) : d304171 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30733, d304171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30733, d304171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77661 (p : Pattern) (ha : d30740 p = 1) (hb : d300100 p = 1) : d304178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d300100 q = 1) : d304091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77642 q ha hb
    | true =>
      simp only [d30651, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d300100 q = 1) : d304092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77623 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30653 q = 1) (hb : d300100 q = 1) : d304093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30653, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30653, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30738 q = 1) (hb : d300100 q = 1) : d304176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30738, d304176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30738, d304176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30739 q = 1) (hb : d300100 q = 1) : d304177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30739, d304177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30739, d304177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30740 q = 1) (hb : d300100 q = 1) : d304178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30740, d304178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30740, d304178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77662 (p : Pattern) (ha : d30744 p = 1) (hb : d300100 p = 1) : d304183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d129 q = 1) : d129 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130 q = 1) (hb : d216468 q = 1) : d534 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d216468, d534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130, d216468, d534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d311 q = 1) (hb : d300099 q = 1) : d304182 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d311, d300099, d304182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d311, d300099, d304182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30744 q = 1) (hb : d300100 q = 1) : d304183 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d30744, d300100, d304183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30744, d300100, d304183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77663 (p : Pattern) (ha : d30750 p = 1) (hb : d300100 p = 1) : d304189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30745 q = 1) (hb : d300100 q = 1) : d304184 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30745, d304184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77662 q ha hb
    | true =>
      simp only [d30745, d304184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30746 q = 1) (hb : d300100 q = 1) : d304185 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30746, d304185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30746, d304185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25433 q = 1) (hb : d300100 q = 1) : d304073 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d304073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77639 q ha hb
    | true =>
      simp only [d25433, d304073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25434 q = 1) (hb : d300100 q = 1) : d304074 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d304074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25434, d304074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30747 q = 1) (hb : d300100 q = 1) : d304186 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30747, d304186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30747, d304186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77620 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30635 q = 1) (hb : d300100 q = 1) : d304075 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30635, d304075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30635, d304075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30748 q = 1) (hb : d300100 q = 1) : d304187 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30748, d304187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30748, d304187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30749 q = 1) (hb : d300100 q = 1) : d304188 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30749, d304188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30749, d304188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30636 q = 1) (hb : d300100 q = 1) : d304076 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30636, d304076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30636, d304076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30637 q = 1) (hb : d300100 q = 1) : d304077 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30637, d304077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30637, d304077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d30750 q = 1) (hb : d300100 q = 1) : d304189 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30750, d304189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30750, d304189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro77664 (p : Pattern) (ha : d30758 p = 1) (hb : d300100 p = 1) : d304078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25433 q = 1) (hb : d300100 q = 1) : d304073 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d304073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77639 q ha hb
    | true =>
      simp only [d25433, d304073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25434 q = 1) (hb : d300100 q = 1) : d304074 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d304074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25434, d304074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77620 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30635 q = 1) (hb : d300100 q = 1) : d304075 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30635, d304075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30635, d304075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30756 q = 1) (hb : d300100 q = 1) : d304076 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30756, d304076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30756, d304076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30757 q = 1) (hb : d300100 q = 1) : d304077 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30757, d304077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30757, d304077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30758 q = 1) (hb : d300100 q = 1) : d304078 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30758, d304078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30758, d304078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro77665 (p : Pattern) (ha : d30764 p = 1) (hb : d300100 p = 1) : d304195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30751 q = 1) (hb : d300100 q = 1) : d304190 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30751, d304190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77663 q ha hb
    | true =>
      simp only [d30751, d304190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30752 q = 1) (hb : d300100 q = 1) : d304191 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30752, d304191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30752, d304191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30753 q = 1) (hb : d300100 q = 1) : d304192 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30753, d304192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30753, d304192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30754 q = 1) (hb : d300100 q = 1) : d304193 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30754, d304193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30754, d304193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30639 q = 1) (hb : d300100 q = 1) : d304079 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30639, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77640 q ha hb
    | true =>
      simp only [d30639, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30640 q = 1) (hb : d300100 q = 1) : d304080 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30640, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30640, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30641 q = 1) (hb : d300100 q = 1) : d304081 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30641, d304081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30641, d304081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30642 q = 1) (hb : d300100 q = 1) : d304082 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30642, d304082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30642, d304082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30755 q = 1) (hb : d300100 q = 1) : d304194 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30755, d304194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30755, d304194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30759 q = 1) (hb : d300100 q = 1) : d304079 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30759, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77664 q ha hb
    | true =>
      simp only [d30759, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30760 q = 1) (hb : d300100 q = 1) : d304080 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30760, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30760, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30761 q = 1) (hb : d300100 q = 1) : d304081 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30761, d304081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30761, d304081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30762 q = 1) (hb : d300100 q = 1) : d304082 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30762, d304082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30762, d304082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d25 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77621 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d26 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d27 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d30763 q = 1) (hb : d300100 q = 1) : d304083 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30763, d304083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d30763, d304083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d30764 q = 1) (hb : d300100 q = 1) : d304195 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30764, d304195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30764, d304195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro77666 (p : Pattern) (ha : d30770 p = 1) (hb : d300100 p = 1) : d304201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30765 q = 1) (hb : d300100 q = 1) : d304196 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30765, d304196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77665 q ha hb
    | true =>
      simp only [d30765, d304196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77641 q ha hb
  have h2 (q : Pattern) (ha : d30766 q = 1) (hb : d300100 q = 1) : d304197 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30766, d304197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30766, d304197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30767 q = 1) (hb : d300100 q = 1) : d304198 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30767, d304198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30767, d304198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30645 q = 1) (hb : d300100 q = 1) : d304085 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30645, d304085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77641 q ha hb
    | true =>
      simp only [d30645, d304085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77622 q ha hb
  have h5 (q : Pattern) (ha : d30646 q = 1) (hb : d300100 q = 1) : d304086 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30646, d304086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30646, d304086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30647 q = 1) (hb : d300100 q = 1) : d304087 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30647, d304087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30647, d304087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30768 q = 1) (hb : d300100 q = 1) : d304199 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30768, d304199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30768, d304199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77622 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30648 q = 1) (hb : d300100 q = 1) : d304088 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30648, d304088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30648, d304088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30769 q = 1) (hb : d300100 q = 1) : d304200 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d30769, d304200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30769, d304200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30770 q = 1) (hb : d300100 q = 1) : d304201 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d30770, d304201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30770, d304201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro77667 (p : Pattern) (ha : d30776 p = 1) (hb : d300100 p = 1) : d304207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30771 q = 1) (hb : d300100 q = 1) : d304202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30771, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77666 q ha hb
    | true =>
      simp only [d30771, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30772 q = 1) (hb : d300100 q = 1) : d304203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30772, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30772, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30651 q = 1) (hb : d300100 q = 1) : d304091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77642 q ha hb
    | true =>
      simp only [d30651, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30652 q = 1) (hb : d300100 q = 1) : d304092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30773 q = 1) (hb : d300100 q = 1) : d304204 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30773, d304204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30773, d304204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30774 q = 1) (hb : d300100 q = 1) : d304205 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30774, d304205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30774, d304205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30775 q = 1) (hb : d300100 q = 1) : d304206 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30775, d304206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30775, d304206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30776 q = 1) (hb : d300100 q = 1) : d304207 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30776, d304207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30776, d304207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77668 (p : Pattern) (ha : d30805 p = 1) (hb : d300100 p = 1) : d304096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d300100 q = 1) : d304091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77642 q ha hb
    | true =>
      simp only [d30651, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d300100 q = 1) : d304092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30802 q = 1) (hb : d300100 q = 1) : d304093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30802, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30802, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30803 q = 1) (hb : d300100 q = 1) : d304094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30803, d304094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30803, d304094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30804 q = 1) (hb : d300100 q = 1) : d304095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30804, d304095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30804, d304095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30805 q = 1) (hb : d300100 q = 1) : d304096 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30805, d304096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30805, d304096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77669 (p : Pattern) (ha : d245392 p = 1) (hb : d300100 p = 1) : d304213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30734 q = 1) (hb : d300100 q = 1) : d304172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30734, d304172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77660 q ha hb
    | true =>
      simp only [d30734, d304172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77637 q ha hb
  have h2 (q : Pattern) (ha : d30735 q = 1) (hb : d300100 q = 1) : d304173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30735, d304173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30735, d304173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30736 q = 1) (hb : d300100 q = 1) : d304174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30736, d304174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30736, d304174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30737 q = 1) (hb : d300100 q = 1) : d304175 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30737, d304175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30737, d304175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30741 q = 1) (hb : d300100 q = 1) : d304179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30741, d304179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77661 q ha hb
    | true =>
      simp only [d30741, d304179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77638 q ha hb
  have h6 (q : Pattern) (ha : d30742 q = 1) (hb : d300100 q = 1) : d304180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30742, d304180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30742, d304180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30743 q = 1) (hb : d300100 q = 1) : d304181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30743, d304181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30743, d304181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30777 q = 1) (hb : d300100 q = 1) : d304208 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30777, d304208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77667 q ha hb
    | true =>
      simp only [d30777, d304208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77643 q ha hb
  have h9 (q : Pattern) (ha : d245388 q = 1) (hb : d300100 q = 1) : d304209 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245388, d304209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245388, d304209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30806 q = 1) (hb : d300100 q = 1) : d304097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30806, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77668 q ha hb
    | true =>
      simp only [d30806, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30807 q = 1) (hb : d300100 q = 1) : d304098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30807, d304098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30807, d304098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245389 q = 1) (hb : d300100 q = 1) : d304210 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245389, d304210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245389, d304210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245390 q = 1) (hb : d300100 q = 1) : d304211 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245390, d304211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245390, d304211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245391 q = 1) (hb : d300100 q = 1) : d304212 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245391, d304212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245391, d304212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d245392 q = 1) (hb : d300100 q = 1) : d304213 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245392, d304213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245392, d304213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro77670 (p : Pattern) (ha : d30812 p = 1) (hb : d300100 p = 1) : d304214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d300100 q = 1) : d304091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77642 q ha hb
    | true =>
      simp only [d30651, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d300100 q = 1) : d304092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77623 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30653 q = 1) (hb : d300100 q = 1) : d304093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30653, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30653, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30654 q = 1) (hb : d300100 q = 1) : d304094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30654, d304094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30654, d304094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30732 q = 1) (hb : d300100 q = 1) : d304170 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30732, d304170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30732, d304170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30812 q = 1) (hb : d300100 q = 1) : d304214 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30812, d304214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30812, d304214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro77671 (p : Pattern) (ha : d30817 p = 1) (hb : d300100 p = 1) : d304219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d300100 q = 1) : d304091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77642 q ha hb
    | true =>
      simp only [d30651, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d300100 q = 1) : d304092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77623 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30653 q = 1) (hb : d300100 q = 1) : d304093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30653, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30653, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30738 q = 1) (hb : d300100 q = 1) : d304176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30738, d304176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30738, d304176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30739 q = 1) (hb : d300100 q = 1) : d304177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30739, d304177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30739, d304177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30817 q = 1) (hb : d300100 q = 1) : d304219 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30817, d304219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30817, d304219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro77672 (p : Pattern) (ha : d30821 p = 1) (hb : d300100 p = 1) : d304223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30771 q = 1) (hb : d300100 q = 1) : d304202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30771, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77666 q ha hb
    | true =>
      simp only [d30771, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30772 q = 1) (hb : d300100 q = 1) : d304203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30772, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30772, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30651 q = 1) (hb : d300100 q = 1) : d304091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77642 q ha hb
    | true =>
      simp only [d30651, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30652 q = 1) (hb : d300100 q = 1) : d304092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30773 q = 1) (hb : d300100 q = 1) : d304204 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30773, d304204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30773, d304204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30774 q = 1) (hb : d300100 q = 1) : d304205 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30774, d304205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30774, d304205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30775 q = 1) (hb : d300100 q = 1) : d304206 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30775, d304206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30775, d304206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30821 q = 1) (hb : d300100 q = 1) : d304223 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30821, d304223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30821, d304223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro77673 (p : Pattern) (ha : d30826 p = 1) (hb : d300100 p = 1) : d304103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d300100 q = 1) : d304091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77642 q ha hb
    | true =>
      simp only [d30651, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d300100 q = 1) : d304092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30802 q = 1) (hb : d300100 q = 1) : d304093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30802, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30802, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30803 q = 1) (hb : d300100 q = 1) : d304094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30803, d304094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30803, d304094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30804 q = 1) (hb : d300100 q = 1) : d304095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30804, d304095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30804, d304095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30826 q = 1) (hb : d300100 q = 1) : d304103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30826, d304103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30826, d304103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77674 (p : Pattern) (ha : d245397 p = 1) (hb : d300100 p = 1) : d304229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30734 q = 1) (hb : d300100 q = 1) : d304172 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30734, d304172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77660 q ha hb
    | true =>
      simp only [d30734, d304172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77637 q ha hb
  have h2 (q : Pattern) (ha : d30735 q = 1) (hb : d300100 q = 1) : d304173 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30735, d304173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30735, d304173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30736 q = 1) (hb : d300100 q = 1) : d304174 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30736, d304174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30736, d304174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30737 q = 1) (hb : d300100 q = 1) : d304175 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30737, d304175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30737, d304175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30741 q = 1) (hb : d300100 q = 1) : d304179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30741, d304179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77661 q ha hb
    | true =>
      simp only [d30741, d304179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77638 q ha hb
  have h6 (q : Pattern) (ha : d30742 q = 1) (hb : d300100 q = 1) : d304180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30742, d304180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30742, d304180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30743 q = 1) (hb : d300100 q = 1) : d304181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30743, d304181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30743, d304181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30777 q = 1) (hb : d300100 q = 1) : d304208 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30777, d304208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77667 q ha hb
    | true =>
      simp only [d30777, d304208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77643 q ha hb
  have h9 (q : Pattern) (ha : d245388 q = 1) (hb : d300100 q = 1) : d304209 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245388, d304209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245388, d304209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30806 q = 1) (hb : d300100 q = 1) : d304097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30806, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77668 q ha hb
    | true =>
      simp only [d30806, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30807 q = 1) (hb : d300100 q = 1) : d304098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30807, d304098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30807, d304098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245389 q = 1) (hb : d300100 q = 1) : d304210 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245389, d304210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245389, d304210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245390 q = 1) (hb : d300100 q = 1) : d304211 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245390, d304211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245390, d304211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245391 q = 1) (hb : d300100 q = 1) : d304212 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245391, d304212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245391, d304212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d30813 q = 1) (hb : d300100 q = 1) : d304215 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30813, d304215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77670 q ha hb
    | true =>
      simp only [d30813, d304215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77645 q ha hb
  have h16 (q : Pattern) (ha : d30814 q = 1) (hb : d300100 q = 1) : d304216 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30814, d304216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30814, d304216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d30815 q = 1) (hb : d300100 q = 1) : d304217 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30815, d304217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d30815, d304217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d30816 q = 1) (hb : d300100 q = 1) : d304218 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30816, d304218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30816, d304218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d30818 q = 1) (hb : d300100 q = 1) : d304220 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30818, d304220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77671 q ha hb
    | true =>
      simp only [d30818, d304220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77646 q ha hb
  have h20 (q : Pattern) (ha : d30819 q = 1) (hb : d300100 q = 1) : d304221 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30819, d304221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30819, d304221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d30820 q = 1) (hb : d300100 q = 1) : d304222 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30820, d304222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d30820, d304222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d30822 q = 1) (hb : d300100 q = 1) : d304224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30822, d304224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77672 q ha hb
    | true =>
      simp only [d30822, d304224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77647 q ha hb
  have h23 (q : Pattern) (ha : d245393 q = 1) (hb : d300100 q = 1) : d304225 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245393, d304225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d245393, d304225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d30827 q = 1) (hb : d300100 q = 1) : d304104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30827, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77673 q ha hb
    | true =>
      simp only [d30827, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d30828 q = 1) (hb : d300100 q = 1) : d304105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30828, d304105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d30828, d304105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d245394 q = 1) (hb : d300100 q = 1) : d304226 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245394, d304226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d245394, d304226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d245395 q = 1) (hb : d300100 q = 1) : d304227 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245395, d304227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d245395, d304227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d245396 q = 1) (hb : d300100 q = 1) : d304228 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245396, d304228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d245396, d304228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d245397 q = 1) (hb : d300100 q = 1) : d304229 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245397, d304229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245397, d304229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro77675 (p : Pattern) (ha : d245404 p = 1) (hb : d300100 p = 1) : d304238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30822 q = 1) (hb : d300100 q = 1) : d304224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30822, d304224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77672 q ha hb
    | true =>
      simp only [d30822, d304224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77647 q ha hb
  have h2 (q : Pattern) (ha : d245393 q = 1) (hb : d300100 q = 1) : d304225 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245393, d304225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245393, d304225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30827 q = 1) (hb : d300100 q = 1) : d304104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30827, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77673 q ha hb
    | true =>
      simp only [d30827, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30828 q = 1) (hb : d300100 q = 1) : d304105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30828, d304105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30828, d304105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245394 q = 1) (hb : d300100 q = 1) : d304226 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245394, d304226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245394, d304226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245402 q = 1) (hb : d300100 q = 1) : d304236 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245402, d304236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245402, d304236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245403 q = 1) (hb : d300100 q = 1) : d304237 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245403, d304237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245403, d304237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245404 q = 1) (hb : d300100 q = 1) : d304238 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245404, d304238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245404, d304238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77676 (p : Pattern) (ha : d30857 p = 1) (hb : d300100 p = 1) : d304249 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30847 q = 1) (hb : d300100 q = 1) : d304244 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30847, d304244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30847, d304244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77663 q ha hb
  have h2 (q : Pattern) (ha : d30751 q = 1) (hb : d300100 q = 1) : d304190 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30751, d304190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77663 q ha hb
    | true =>
      simp only [d30751, d304190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30848 q = 1) (hb : d300100 q = 1) : d304245 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30848, d304245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30848, d304245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30752 q = 1) (hb : d300100 q = 1) : d304191 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30752, d304191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30752, d304191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30849 q = 1) (hb : d300100 q = 1) : d304246 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30849, d304246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30849, d304246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30850 q = 1) (hb : d300100 q = 1) : d304247 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30850, d304247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30850, d304247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30682 q = 1) (hb : d300100 q = 1) : d304120 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30682, d304120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30682, d304120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77640 q ha hb
  have h8 (q : Pattern) (ha : d30639 q = 1) (hb : d300100 q = 1) : d304079 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30639, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77640 q ha hb
    | true =>
      simp only [d30639, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30683 q = 1) (hb : d300100 q = 1) : d304121 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30683, d304121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30683, d304121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30640 q = 1) (hb : d300100 q = 1) : d304080 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30640, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30640, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30684 q = 1) (hb : d300100 q = 1) : d304122 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30684, d304122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30684, d304122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30685 q = 1) (hb : d300100 q = 1) : d304123 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30685, d304123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30685, d304123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30851 q = 1) (hb : d300100 q = 1) : d304248 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30851, d304248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30851, d304248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d30852 q = 1) (hb : d300100 q = 1) : d304120 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30852, d304120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30852, d304120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77664 q ha hb
  have h15 (q : Pattern) (ha : d30759 q = 1) (hb : d300100 q = 1) : d304079 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30759, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77664 q ha hb
    | true =>
      simp only [d30759, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d30853 q = 1) (hb : d300100 q = 1) : d304121 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30853, d304121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d30853, d304121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d30760 q = 1) (hb : d300100 q = 1) : d304080 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30760, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d30760, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d30854 q = 1) (hb : d300100 q = 1) : d304122 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30854, d304122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d30854, d304122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d30855 q = 1) (hb : d300100 q = 1) : d304123 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30855, d304123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d30855, d304123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d66 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77621 q ha hb
  have h21 (q : Pattern) (ha : d25 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77621 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d67 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d26 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d68 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d69 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d30856 q = 1) (hb : d300100 q = 1) : d304124 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30856, d304124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d30856, d304124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d30857 q = 1) (hb : d300100 q = 1) : d304249 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30857, d304249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d30857, d304249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro77677 (p : Pattern) (ha : d30863 p = 1) (hb : d300100 p = 1) : d304255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30858 q = 1) (hb : d300100 q = 1) : d304250 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30858, d304250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77676 q ha hb
    | true =>
      simp only [d30858, d304250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77650 q ha hb
  have h2 (q : Pattern) (ha : d30859 q = 1) (hb : d300100 q = 1) : d304251 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30859, d304251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30859, d304251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30860 q = 1) (hb : d300100 q = 1) : d304252 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30860, d304252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30860, d304252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30688 q = 1) (hb : d300100 q = 1) : d304126 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30688, d304126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77650 q ha hb
    | true =>
      simp only [d30688, d304126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77629 q ha hb
  have h5 (q : Pattern) (ha : d30689 q = 1) (hb : d300100 q = 1) : d304127 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30689, d304127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30689, d304127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30690 q = 1) (hb : d300100 q = 1) : d304128 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30690, d304128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30690, d304128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30861 q = 1) (hb : d300100 q = 1) : d304253 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30861, d304253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30861, d304253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77629 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30691 q = 1) (hb : d300100 q = 1) : d304129 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30691, d304129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30691, d304129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30862 q = 1) (hb : d300100 q = 1) : d304254 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d30862, d304254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30862, d304254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30863 q = 1) (hb : d300100 q = 1) : d304255 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d30863, d304255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30863, d304255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro77678 (p : Pattern) (ha : d30869 p = 1) (hb : d300100 p = 1) : d304261 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30864 q = 1) (hb : d300100 q = 1) : d304256 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30864, d304256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77677 q ha hb
    | true =>
      simp only [d30864, d304256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30865 q = 1) (hb : d300100 q = 1) : d304257 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30865, d304257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30865, d304257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30694 q = 1) (hb : d300100 q = 1) : d304132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30694, d304132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77651 q ha hb
    | true =>
      simp only [d30694, d304132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30695 q = 1) (hb : d300100 q = 1) : d304133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30695, d304133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30695, d304133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30866 q = 1) (hb : d300100 q = 1) : d304258 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30866, d304258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30866, d304258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30867 q = 1) (hb : d300100 q = 1) : d304259 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30867, d304259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30867, d304259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30868 q = 1) (hb : d300100 q = 1) : d304260 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30868, d304260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30868, d304260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30869 q = 1) (hb : d300100 q = 1) : d304261 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30869, d304261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30869, d304261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro77679 (p : Pattern) (ha : d30894 p = 1) (hb : d300100 p = 1) : d304137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30694 q = 1) (hb : d300100 q = 1) : d304132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30694, d304132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77651 q ha hb
    | true =>
      simp only [d30694, d304132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30695 q = 1) (hb : d300100 q = 1) : d304133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30695, d304133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30695, d304133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30891 q = 1) (hb : d300100 q = 1) : d304134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30891, d304134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30891, d304134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30892 q = 1) (hb : d300100 q = 1) : d304135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30892, d304135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30892, d304135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30893 q = 1) (hb : d300100 q = 1) : d304136 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30893, d304136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30893, d304136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30894 q = 1) (hb : d300100 q = 1) : d304137 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30894, d304137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30894, d304137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77680 (p : Pattern) (ha : d245414 p = 1) (hb : d300100 p = 1) : d304267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30870 q = 1) (hb : d300100 q = 1) : d304262 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30870, d304262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77678 q ha hb
    | true =>
      simp only [d30870, d304262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77652 q ha hb
  have h2 (q : Pattern) (ha : d245410 q = 1) (hb : d300100 q = 1) : d304263 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245410, d304263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245410, d304263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30895 q = 1) (hb : d300100 q = 1) : d304138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30895, d304138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77679 q ha hb
    | true =>
      simp only [d30895, d304138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30896 q = 1) (hb : d300100 q = 1) : d304139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30896, d304139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30896, d304139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245411 q = 1) (hb : d300100 q = 1) : d304264 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245411, d304264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245411, d304264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245412 q = 1) (hb : d300100 q = 1) : d304265 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245412, d304265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245412, d304265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245413 q = 1) (hb : d300100 q = 1) : d304266 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245413, d304266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245413, d304266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245414 q = 1) (hb : d300100 q = 1) : d304267 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245414, d304267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245414, d304267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77681 (p : Pattern) (ha : d245420 p = 1) (hb : d300100 p = 1) : d304273 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30722 q = 1) (hb : d300100 q = 1) : d304160 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30722, d304160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30722, d304160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77657 q ha hb
  have h2 (q : Pattern) (ha : d30723 q = 1) (hb : d300100 q = 1) : d304161 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d30723, d304161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30723, d304161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30729 q = 1) (hb : d300100 q = 1) : d304167 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30729, d304167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77657 q ha hb
    | true =>
      simp only [d30729, d304167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77658 q ha hb
  have h4 (q : Pattern) (ha : d30730 q = 1) (hb : d300100 q = 1) : d304168 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d30730, d304168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30730, d304168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30731 q = 1) (hb : d300100 q = 1) : d304169 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d30731, d304169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30731, d304169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245398 q = 1) (hb : d300100 q = 1) : d304230 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245398, d304230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77669 q ha hb
    | true =>
      simp only [d245398, d304230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77674 q ha hb
  have h7 (q : Pattern) (ha : d30835 q = 1) (hb : d300100 q = 1) : d304232 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30835, d304232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77659 q ha hb
    | true =>
      simp only [d30835, d304232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77635 q ha hb
  have h8 (q : Pattern) (ha : d245399 q = 1) (hb : d300100 q = 1) : d304233 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245399, d304233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245399, d304233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245400 q = 1) (hb : d300100 q = 1) : d304234 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245400, d304234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245400, d304234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d245401 q = 1) (hb : d300100 q = 1) : d304235 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245401, d304235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245401, d304235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245405 q = 1) (hb : d300100 q = 1) : d304239 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245405, d304239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245405, d304239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77675 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77655 q ha hb
  have h13 (q : Pattern) (ha : d245406 q = 1) (hb : d300100 q = 1) : d304240 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245406, d304240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245406, d304240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245407 q = 1) (hb : d300100 q = 1) : d304241 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245407, d304241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245407, d304241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245408 q = 1) (hb : d300100 q = 1) : d304242 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245408, d304242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245408, d304242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d245409 q = 1) (hb : d300100 q = 1) : d304243 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245409, d304243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245409, d304243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245415 q = 1) (hb : d300100 q = 1) : d304268 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245415, d304268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245415, d304268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77680 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77656 q ha hb
  have h19 (q : Pattern) (ha : d245416 q = 1) (hb : d300100 q = 1) : d304269 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245416, d304269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245416, d304269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d245417 q = 1) (hb : d300100 q = 1) : d304270 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245417, d304270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d245417, d304270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d245418 q = 1) (hb : d300100 q = 1) : d304271 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245418, d304271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d245418, d304271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d245419 q = 1) (hb : d300100 q = 1) : d304272 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245419, d304272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d245419, d304272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d245420 q = 1) (hb : d300100 q = 1) : d304273 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245420, d304273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245420, d304273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro77682 (p : Pattern) (ha : d245426 p = 1) (hb : d300100 p = 1) : d304279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77633 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245383 q = 1) (hb : d300100 q = 1) : d304150 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245383, d304150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245383, d304150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77654 q ha hb
  have h6 (q : Pattern) (ha : d245384 q = 1) (hb : d300100 q = 1) : d304151 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245384, d304151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245384, d304151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245385 q = 1) (hb : d300100 q = 1) : d304152 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245385, d304152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245385, d304152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245386 q = 1) (hb : d300100 q = 1) : d304153 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245386, d304153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245386, d304153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245387 q = 1) (hb : d300100 q = 1) : d304154 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245387, d304154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245387, d304154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d245421 q = 1) (hb : d300100 q = 1) : d304274 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245421, d304274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245421, d304274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77681 q ha hb
  have h11 (q : Pattern) (ha : d245422 q = 1) (hb : d300100 q = 1) : d304275 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245422, d304275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245422, d304275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d245423 q = 1) (hb : d300100 q = 1) : d304276 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245423, d304276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245423, d304276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245424 q = 1) (hb : d300100 q = 1) : d304277 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245424, d304277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245424, d304277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245425 q = 1) (hb : d300100 q = 1) : d304278 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245425, d304278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245425, d304278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d245426 q = 1) (hb : d300100 q = 1) : d304279 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245426, d304279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245426, d304279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro77683 (p : Pattern) (ha : d30915 p = 1) (hb : d300100 p = 1) : d304201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30765 q = 1) (hb : d300100 q = 1) : d304196 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30765, d304196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77665 q ha hb
    | true =>
      simp only [d30765, d304196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77641 q ha hb
  have h2 (q : Pattern) (ha : d30766 q = 1) (hb : d300100 q = 1) : d304197 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30766, d304197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30766, d304197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30767 q = 1) (hb : d300100 q = 1) : d304198 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30767, d304198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30767, d304198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30645 q = 1) (hb : d300100 q = 1) : d304085 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30645, d304085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77641 q ha hb
    | true =>
      simp only [d30645, d304085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77622 q ha hb
  have h5 (q : Pattern) (ha : d30646 q = 1) (hb : d300100 q = 1) : d304086 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30646, d304086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30646, d304086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30647 q = 1) (hb : d300100 q = 1) : d304087 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30647, d304087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30647, d304087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30768 q = 1) (hb : d300100 q = 1) : d304199 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30768, d304199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30768, d304199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30913 q = 1) (hb : d300100 q = 1) : d304088 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30913, d304088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30913, d304088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30914 q = 1) (hb : d300100 q = 1) : d304200 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d30914, d304200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30914, d304200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30915 q = 1) (hb : d300100 q = 1) : d304201 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d30915, d304201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30915, d304201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro77684 (p : Pattern) (ha : d30919 p = 1) (hb : d300100 p = 1) : d304090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30645 q = 1) (hb : d300100 q = 1) : d304085 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30645, d304085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77641 q ha hb
    | true =>
      simp only [d30645, d304085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77622 q ha hb
  have h2 (q : Pattern) (ha : d30646 q = 1) (hb : d300100 q = 1) : d304086 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30646, d304086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30646, d304086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30647 q = 1) (hb : d300100 q = 1) : d304087 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30647, d304087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30647, d304087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30913 q = 1) (hb : d300100 q = 1) : d304088 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30913, d304088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30913, d304088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30918 q = 1) (hb : d300100 q = 1) : d304089 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d30918, d304089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30918, d304089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30919 q = 1) (hb : d300100 q = 1) : d304090 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d30919, d304090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30919, d304090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77685 (p : Pattern) (ha : d30925 p = 1) (hb : d300100 p = 1) : d304207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d300100 q = 1) : d304202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77683 q ha hb
    | true =>
      simp only [d30916, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d300100 q = 1) : d304203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30920 q = 1) (hb : d300100 q = 1) : d304091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77684 q ha hb
    | true =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30921 q = 1) (hb : d300100 q = 1) : d304092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30922 q = 1) (hb : d300100 q = 1) : d304204 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30922, d304204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30922, d304204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30923 q = 1) (hb : d300100 q = 1) : d304205 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30923, d304205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30923, d304205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30924 q = 1) (hb : d300100 q = 1) : d304206 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30924, d304206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30924, d304206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30925 q = 1) (hb : d300100 q = 1) : d304207 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30925, d304207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30925, d304207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77686 (p : Pattern) (ha : d30929 p = 1) (hb : d300100 p = 1) : d304096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30920 q = 1) (hb : d300100 q = 1) : d304091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77684 q ha hb
    | true =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30921 q = 1) (hb : d300100 q = 1) : d304092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30926 q = 1) (hb : d300100 q = 1) : d304093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30926, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30926, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30927 q = 1) (hb : d300100 q = 1) : d304094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30927, d304094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30927, d304094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30928 q = 1) (hb : d300100 q = 1) : d304095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30928, d304095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30928, d304095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30929 q = 1) (hb : d300100 q = 1) : d304096 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30929, d304096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30929, d304096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77687 (p : Pattern) (ha : d30935 p = 1) (hb : d300100 p = 1) : d304284 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30930 q = 1) (hb : d300100 q = 1) : d304208 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30930, d304208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77685 q ha hb
    | true =>
      simp only [d30930, d304208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77686 q ha hb
  have h2 (q : Pattern) (ha : d30931 q = 1) (hb : d300100 q = 1) : d304280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30931, d304280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30931, d304280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30932 q = 1) (hb : d300100 q = 1) : d304281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30932, d304281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30932, d304281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30933 q = 1) (hb : d300100 q = 1) : d304282 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30933, d304282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30933, d304282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30934 q = 1) (hb : d300100 q = 1) : d304283 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30934, d304283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30934, d304283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30935 q = 1) (hb : d300100 q = 1) : d304284 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d30935, d304284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30935, d304284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77688 (p : Pattern) (ha : d30938 p = 1) (hb : d300100 p = 1) : d304223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d300100 q = 1) : d304202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77683 q ha hb
    | true =>
      simp only [d30916, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d300100 q = 1) : d304203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30920 q = 1) (hb : d300100 q = 1) : d304091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77684 q ha hb
    | true =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30921 q = 1) (hb : d300100 q = 1) : d304092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30922 q = 1) (hb : d300100 q = 1) : d304204 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30922, d304204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30922, d304204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30923 q = 1) (hb : d300100 q = 1) : d304205 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30923, d304205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30923, d304205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30924 q = 1) (hb : d300100 q = 1) : d304206 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30924, d304206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30924, d304206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30938 q = 1) (hb : d300100 q = 1) : d304223 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30938, d304223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30938, d304223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro77689 (p : Pattern) (ha : d30939 p = 1) (hb : d300100 p = 1) : d304103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30920 q = 1) (hb : d300100 q = 1) : d304091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77684 q ha hb
    | true =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30921 q = 1) (hb : d300100 q = 1) : d304092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30926 q = 1) (hb : d300100 q = 1) : d304093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30926, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30926, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30927 q = 1) (hb : d300100 q = 1) : d304094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30927, d304094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30927, d304094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30928 q = 1) (hb : d300100 q = 1) : d304095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30928, d304095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30928, d304095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30939 q = 1) (hb : d300100 q = 1) : d304103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30939, d304103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30939, d304103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77690 (p : Pattern) (ha : d30945 p = 1) (hb : d300100 p = 1) : d304291 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30930 q = 1) (hb : d300100 q = 1) : d304208 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30930, d304208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77685 q ha hb
    | true =>
      simp only [d30930, d304208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77686 q ha hb
  have h2 (q : Pattern) (ha : d30931 q = 1) (hb : d300100 q = 1) : d304280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30931, d304280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30931, d304280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30932 q = 1) (hb : d300100 q = 1) : d304281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30932, d304281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30932, d304281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30933 q = 1) (hb : d300100 q = 1) : d304282 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30933, d304282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30933, d304282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30934 q = 1) (hb : d300100 q = 1) : d304283 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30934, d304283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30934, d304283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30940 q = 1) (hb : d300100 q = 1) : d304224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30940, d304224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77688 q ha hb
    | true =>
      simp only [d30940, d304224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77689 q ha hb
  have h7 (q : Pattern) (ha : d30941 q = 1) (hb : d300100 q = 1) : d304287 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30941, d304287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30941, d304287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30942 q = 1) (hb : d300100 q = 1) : d304288 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30942, d304288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30942, d304288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30943 q = 1) (hb : d300100 q = 1) : d304289 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30943, d304289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30943, d304289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30944 q = 1) (hb : d300100 q = 1) : d304290 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30944, d304290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30944, d304290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30945 q = 1) (hb : d300100 q = 1) : d304291 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d30945, d304291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30945, d304291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro77691 (p : Pattern) (ha : d31097 p = 1) (hb : d300100 p = 1) : d304372 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30930 q = 1) (hb : d300100 q = 1) : d304208 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30930, d304208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77685 q ha hb
    | true =>
      simp only [d30930, d304208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77686 q ha hb
  have h2 (q : Pattern) (ha : d30931 q = 1) (hb : d300100 q = 1) : d304280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30931, d304280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30931, d304280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30932 q = 1) (hb : d300100 q = 1) : d304281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30932, d304281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30932, d304281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30933 q = 1) (hb : d300100 q = 1) : d304282 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30933, d304282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30933, d304282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30934 q = 1) (hb : d300100 q = 1) : d304283 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30934, d304283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30934, d304283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31092 q = 1) (hb : d300100 q = 1) : d304097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31092, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77686 q ha hb
    | true =>
      simp only [d31092, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31093 q = 1) (hb : d300100 q = 1) : d304155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31093, d304155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31093, d304155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31094 q = 1) (hb : d300100 q = 1) : d304156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31094, d304156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31094, d304156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31095 q = 1) (hb : d300100 q = 1) : d304157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31095, d304157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31095, d304157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31096 q = 1) (hb : d300100 q = 1) : d304158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31096, d304158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31096, d304158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31097 q = 1) (hb : d300100 q = 1) : d304372 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31097, d304372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31097, d304372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro77692 (p : Pattern) (ha : d31103 p = 1) (hb : d300100 p = 1) : d304166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31092 q = 1) (hb : d300100 q = 1) : d304097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31092, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77686 q ha hb
    | true =>
      simp only [d31092, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31093 q = 1) (hb : d300100 q = 1) : d304155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31093, d304155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31093, d304155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31094 q = 1) (hb : d300100 q = 1) : d304156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31094, d304156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31094, d304156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31095 q = 1) (hb : d300100 q = 1) : d304157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31095, d304157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31095, d304157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31096 q = 1) (hb : d300100 q = 1) : d304158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31096, d304158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31096, d304158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31098 q = 1) (hb : d300100 q = 1) : d304104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31098, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77689 q ha hb
    | true =>
      simp only [d31098, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31099 q = 1) (hb : d300100 q = 1) : d304162 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31099, d304162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31099, d304162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31100 q = 1) (hb : d300100 q = 1) : d304163 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31100, d304163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31100, d304163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31101 q = 1) (hb : d300100 q = 1) : d304164 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31101, d304164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31101, d304164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31102 q = 1) (hb : d300100 q = 1) : d304165 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31102, d304165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31102, d304165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31103 q = 1) (hb : d300100 q = 1) : d304166 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31103, d304166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31103, d304166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro77693 (p : Pattern) (ha : d31112 p = 1) (hb : d300100 p = 1) : d304381 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31098 q = 1) (hb : d300100 q = 1) : d304104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31098, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77689 q ha hb
    | true =>
      simp only [d31098, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31099 q = 1) (hb : d300100 q = 1) : d304162 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31099, d304162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31099, d304162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31100 q = 1) (hb : d300100 q = 1) : d304163 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31100, d304163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31100, d304163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31101 q = 1) (hb : d300100 q = 1) : d304164 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31101, d304164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31101, d304164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31102 q = 1) (hb : d300100 q = 1) : d304165 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31102, d304165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31102, d304165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31112 q = 1) (hb : d300100 q = 1) : d304381 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31112, d304381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31112, d304381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77694 (p : Pattern) (ha : d31155 p = 1) (hb : d300100 p = 1) : d304131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30688 q = 1) (hb : d300100 q = 1) : d304126 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30688, d304126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77650 q ha hb
    | true =>
      simp only [d30688, d304126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77629 q ha hb
  have h2 (q : Pattern) (ha : d30689 q = 1) (hb : d300100 q = 1) : d304127 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30689, d304127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30689, d304127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30690 q = 1) (hb : d300100 q = 1) : d304128 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30690, d304128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30690, d304128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31145 q = 1) (hb : d300100 q = 1) : d304129 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31145, d304129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31145, d304129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31154 q = 1) (hb : d300100 q = 1) : d304130 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31154, d304130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31154, d304130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31155 q = 1) (hb : d300100 q = 1) : d304131 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31155, d304131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31155, d304131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77695 (p : Pattern) (ha : d31211 p = 1) (hb : d300100 p = 1) : d304137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31156 q = 1) (hb : d300100 q = 1) : d304132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31156, d304132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77694 q ha hb
    | true =>
      simp only [d31156, d304132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31157 q = 1) (hb : d300100 q = 1) : d304133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31157, d304133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31157, d304133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31208 q = 1) (hb : d300100 q = 1) : d304134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31208, d304134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31208, d304134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31209 q = 1) (hb : d300100 q = 1) : d304135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31209, d304135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31209, d304135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31210 q = 1) (hb : d300100 q = 1) : d304136 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31210, d304136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31210, d304136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31211 q = 1) (hb : d300100 q = 1) : d304137 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31211, d304137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31211, d304137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77696 (p : Pattern) (ha : d31217 p = 1) (hb : d300100 p = 1) : d304427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31212 q = 1) (hb : d300100 q = 1) : d304138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31212, d304138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77695 q ha hb
    | true =>
      simp only [d31212, d304138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31213 q = 1) (hb : d300100 q = 1) : d304423 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31213, d304423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31213, d304423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31214 q = 1) (hb : d300100 q = 1) : d304424 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31214, d304424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31214, d304424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31215 q = 1) (hb : d300100 q = 1) : d304425 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31215, d304425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31215, d304425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31216 q = 1) (hb : d300100 q = 1) : d304426 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31216, d304426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31216, d304426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31217 q = 1) (hb : d300100 q = 1) : d304427 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31217, d304427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31217, d304427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77697 (p : Pattern) (ha : d30950 p = 1) (hb : d300100 p = 1) : d304296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d300100 q = 1) : d304202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77683 q ha hb
    | true =>
      simp only [d30916, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d300100 q = 1) : d304203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30920 q = 1) (hb : d300100 q = 1) : d304091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77684 q ha hb
    | true =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30921 q = 1) (hb : d300100 q = 1) : d304092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30922 q = 1) (hb : d300100 q = 1) : d304204 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30922, d304204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30922, d304204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30923 q = 1) (hb : d300100 q = 1) : d304205 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30923, d304205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30923, d304205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30949 q = 1) (hb : d300100 q = 1) : d304295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30949, d304295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30949, d304295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30950 q = 1) (hb : d300100 q = 1) : d304296 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30950, d304296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30950, d304296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77698 (p : Pattern) (ha : d30952 p = 1) (hb : d300100 p = 1) : d304171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30920 q = 1) (hb : d300100 q = 1) : d304091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77684 q ha hb
    | true =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30921 q = 1) (hb : d300100 q = 1) : d304092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30926 q = 1) (hb : d300100 q = 1) : d304093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30926, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30926, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30927 q = 1) (hb : d300100 q = 1) : d304094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30927, d304094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30927, d304094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30951 q = 1) (hb : d300100 q = 1) : d304170 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30951, d304170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30951, d304170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30952 q = 1) (hb : d300100 q = 1) : d304171 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30952, d304171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30952, d304171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77699 (p : Pattern) (ha : d30959 p = 1) (hb : d300100 p = 1) : d304303 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d300100 q = 1) : d304202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77683 q ha hb
    | true =>
      simp only [d30916, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d300100 q = 1) : d304203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30920 q = 1) (hb : d300100 q = 1) : d304091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77684 q ha hb
    | true =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30921 q = 1) (hb : d300100 q = 1) : d304092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30922 q = 1) (hb : d300100 q = 1) : d304204 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30922, d304204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30922, d304204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30957 q = 1) (hb : d300100 q = 1) : d304301 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30957, d304301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30957, d304301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30958 q = 1) (hb : d300100 q = 1) : d304302 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30958, d304302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30958, d304302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30959 q = 1) (hb : d300100 q = 1) : d304303 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30959, d304303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30959, d304303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77700 (p : Pattern) (ha : d30962 p = 1) (hb : d300100 p = 1) : d304178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30920 q = 1) (hb : d300100 q = 1) : d304091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77684 q ha hb
    | true =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30921 q = 1) (hb : d300100 q = 1) : d304092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30926 q = 1) (hb : d300100 q = 1) : d304093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30926, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30926, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30960 q = 1) (hb : d300100 q = 1) : d304176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30960, d304176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30960, d304176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30961 q = 1) (hb : d300100 q = 1) : d304177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30961, d304177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30961, d304177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30962 q = 1) (hb : d300100 q = 1) : d304178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30962, d304178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30962, d304178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77701 (p : Pattern) (ha : d30966 p = 1) (hb : d300100 p = 1) : d304307 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d528 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d309 q = 1) : d309 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d310 q = 1) (hb : d216468 q = 1) : d825 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d216468, d825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d310, d216468, d825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d529 q = 1) (hb : d300099 q = 1) : d36333 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d529, d300099, d36333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d529, d300099, d36333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30966 q = 1) (hb : d300100 q = 1) : d304307 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d30966, d300100, d304307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30966, d300100, d304307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77702 (p : Pattern) (ha : d30970 p = 1) (hb : d300100 p = 1) : d304183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d534 q = 1) (hb : d216468 q = 1) : d534 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d535 q = 1) (hb : d300099 q = 1) : d304182 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d535, d300099, d304182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d535, d300099, d304182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30970 q = 1) (hb : d300100 q = 1) : d304183 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d30970, d300100, d304183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30970, d300100, d304183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro77703 (p : Pattern) (ha : d30976 p = 1) (hb : d300100 p = 1) : d304313 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30967 q = 1) (hb : d300100 q = 1) : d304308 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30967, d304308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77701 q ha hb
    | true =>
      simp only [d30967, d304308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30968 q = 1) (hb : d300100 q = 1) : d304309 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30968, d304309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30968, d304309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30745 q = 1) (hb : d300100 q = 1) : d304184 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30745, d304184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77662 q ha hb
    | true =>
      simp only [d30745, d304184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30746 q = 1) (hb : d300100 q = 1) : d304185 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30746, d304185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30746, d304185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30969 q = 1) (hb : d300100 q = 1) : d304310 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30969, d304310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30969, d304310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30971 q = 1) (hb : d300100 q = 1) : d304184 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30971, d304184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77702 q ha hb
    | true =>
      simp only [d30971, d304184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30972 q = 1) (hb : d300100 q = 1) : d304185 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30972, d304185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30972, d304185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25433 q = 1) (hb : d300100 q = 1) : d304073 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d304073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77639 q ha hb
    | true =>
      simp only [d25433, d304073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25434 q = 1) (hb : d300100 q = 1) : d304074 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d304074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25434, d304074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30973 q = 1) (hb : d300100 q = 1) : d304186 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30973, d304186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30973, d304186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30974 q = 1) (hb : d300100 q = 1) : d304311 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30974, d304311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30974, d304311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30975 q = 1) (hb : d300100 q = 1) : d304312 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30975, d304312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30975, d304312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30747 q = 1) (hb : d300100 q = 1) : d304186 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30747, d304186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30747, d304186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h14 (q : Pattern) (ha : d19 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77620 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d20 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d30635 q = 1) (hb : d300100 q = 1) : d304075 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30635, d304075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30635, d304075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d30748 q = 1) (hb : d300100 q = 1) : d304187 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30748, d304187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d30748, d304187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d30749 q = 1) (hb : d300100 q = 1) : d304188 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30749, d304188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d30749, d304188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d30976 q = 1) (hb : d300100 q = 1) : d304313 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30976, d304313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30976, d304313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro77704 (p : Pattern) (ha : d30981 p = 1) (hb : d300100 p = 1) : d304189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30745 q = 1) (hb : d300100 q = 1) : d304184 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30745, d304184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77662 q ha hb
    | true =>
      simp only [d30745, d304184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30746 q = 1) (hb : d300100 q = 1) : d304185 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30746, d304185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30746, d304185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25433 q = 1) (hb : d300100 q = 1) : d304073 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d304073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77639 q ha hb
    | true =>
      simp only [d25433, d304073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25434 q = 1) (hb : d300100 q = 1) : d304074 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d304074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25434, d304074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30747 q = 1) (hb : d300100 q = 1) : d304186 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30747, d304186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30747, d304186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77620 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30635 q = 1) (hb : d300100 q = 1) : d304075 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30635, d304075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30635, d304075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30748 q = 1) (hb : d300100 q = 1) : d304187 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30748, d304187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30748, d304187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30749 q = 1) (hb : d300100 q = 1) : d304188 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30749, d304188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30749, d304188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30756 q = 1) (hb : d300100 q = 1) : d304076 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30756, d304076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30756, d304076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30757 q = 1) (hb : d300100 q = 1) : d304077 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30757, d304077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30757, d304077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30981 q = 1) (hb : d300100 q = 1) : d304189 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30981, d304189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30981, d304189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro77705 (p : Pattern) (ha : d30989 p = 1) (hb : d300100 p = 1) : d304321 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30745 q = 1) (hb : d300100 q = 1) : d304184 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d30745, d304184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77662 q ha hb
    | true =>
      simp only [d30745, d304184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30746 q = 1) (hb : d300100 q = 1) : d304185 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d30746, d304185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30746, d304185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25433 q = 1) (hb : d300100 q = 1) : d304073 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d304073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77639 q ha hb
    | true =>
      simp only [d25433, d304073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25434 q = 1) (hb : d300100 q = 1) : d304074 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d304074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25434, d304074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30747 q = 1) (hb : d300100 q = 1) : d304186 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30747, d304186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30747, d304186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30987 q = 1) (hb : d300100 q = 1) : d304319 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30987, d304319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30987, d304319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30988 q = 1) (hb : d300100 q = 1) : d304320 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30988, d304320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30988, d304320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77620 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30635 q = 1) (hb : d300100 q = 1) : d304075 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30635, d304075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30635, d304075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30756 q = 1) (hb : d300100 q = 1) : d304076 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30756, d304076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30756, d304076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30757 q = 1) (hb : d300100 q = 1) : d304077 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30757, d304077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30757, d304077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30989 q = 1) (hb : d300100 q = 1) : d304321 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30989, d304321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30989, d304321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro77706 (p : Pattern) (ha : d30995 p = 1) (hb : d300100 p = 1) : d304327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30977 q = 1) (hb : d300100 q = 1) : d304314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30977, d304314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77703 q ha hb
    | true =>
      simp only [d30977, d304314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30978 q = 1) (hb : d300100 q = 1) : d304315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30978, d304315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30978, d304315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30979 q = 1) (hb : d300100 q = 1) : d304316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30979, d304316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30979, d304316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30980 q = 1) (hb : d300100 q = 1) : d304317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30980, d304317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30980, d304317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30982 q = 1) (hb : d300100 q = 1) : d304190 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30982, d304190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77704 q ha hb
    | true =>
      simp only [d30982, d304190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30983 q = 1) (hb : d300100 q = 1) : d304191 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30983, d304191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30983, d304191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30984 q = 1) (hb : d300100 q = 1) : d304192 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30984, d304192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30984, d304192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30985 q = 1) (hb : d300100 q = 1) : d304193 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30985, d304193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30985, d304193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30986 q = 1) (hb : d300100 q = 1) : d304318 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30986, d304318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30986, d304318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30990 q = 1) (hb : d300100 q = 1) : d304322 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30990, d304322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77705 q ha hb
    | true =>
      simp only [d30990, d304322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30991 q = 1) (hb : d300100 q = 1) : d304323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30991, d304323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30991, d304323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30992 q = 1) (hb : d300100 q = 1) : d304324 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30992, d304324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30992, d304324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30993 q = 1) (hb : d300100 q = 1) : d304325 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30993, d304325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30993, d304325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d30759 q = 1) (hb : d300100 q = 1) : d304079 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30759, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77664 q ha hb
    | true =>
      simp only [d30759, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d30760 q = 1) (hb : d300100 q = 1) : d304080 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30760, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d30760, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d30761 q = 1) (hb : d300100 q = 1) : d304081 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30761, d304081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30761, d304081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d30762 q = 1) (hb : d300100 q = 1) : d304082 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30762, d304082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d30762, d304082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d30994 q = 1) (hb : d300100 q = 1) : d304326 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30994, d304326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d30994, d304326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d30995 q = 1) (hb : d300100 q = 1) : d304327 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30995, d304327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30995, d304327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro77707 (p : Pattern) (ha : d30999 p = 1) (hb : d300100 p = 1) : d304084 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30759 q = 1) (hb : d300100 q = 1) : d304079 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30759, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77664 q ha hb
    | true =>
      simp only [d30759, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30760 q = 1) (hb : d300100 q = 1) : d304080 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30760, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30760, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30761 q = 1) (hb : d300100 q = 1) : d304081 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30761, d304081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30761, d304081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30762 q = 1) (hb : d300100 q = 1) : d304082 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30762, d304082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30762, d304082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77621 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30763 q = 1) (hb : d300100 q = 1) : d304083 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30763, d304083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30763, d304083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30999 q = 1) (hb : d300100 q = 1) : d304084 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30999, d304084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30999, d304084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro77708 (p : Pattern) (ha : d31005 p = 1) (hb : d300100 p = 1) : d304333 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30996 q = 1) (hb : d300100 q = 1) : d304328 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30996, d304328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77706 q ha hb
    | true =>
      simp only [d30996, d304328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77665 q ha hb
  have h2 (q : Pattern) (ha : d30997 q = 1) (hb : d300100 q = 1) : d304329 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30997, d304329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30997, d304329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30998 q = 1) (hb : d300100 q = 1) : d304330 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30998, d304330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30998, d304330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31000 q = 1) (hb : d300100 q = 1) : d304196 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31000, d304196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77665 q ha hb
    | true =>
      simp only [d31000, d304196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77707 q ha hb
  have h5 (q : Pattern) (ha : d31001 q = 1) (hb : d300100 q = 1) : d304197 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31001, d304197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31001, d304197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31002 q = 1) (hb : d300100 q = 1) : d304198 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31002, d304198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31002, d304198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31003 q = 1) (hb : d300100 q = 1) : d304331 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31003, d304331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31003, d304331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30765 q = 1) (hb : d300100 q = 1) : d304196 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30765, d304196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77665 q ha hb
    | true =>
      simp only [d30765, d304196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77641 q ha hb
  have h9 (q : Pattern) (ha : d30766 q = 1) (hb : d300100 q = 1) : d304197 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30766, d304197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30766, d304197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30767 q = 1) (hb : d300100 q = 1) : d304198 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30767, d304198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30767, d304198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30645 q = 1) (hb : d300100 q = 1) : d304085 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30645, d304085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77641 q ha hb
    | true =>
      simp only [d30645, d304085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77622 q ha hb
  have h12 (q : Pattern) (ha : d30646 q = 1) (hb : d300100 q = 1) : d304086 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30646, d304086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30646, d304086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30647 q = 1) (hb : d300100 q = 1) : d304087 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30647, d304087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30647, d304087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d30768 q = 1) (hb : d300100 q = 1) : d304199 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30768, d304199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30768, d304199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d31004 q = 1) (hb : d300100 q = 1) : d304332 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31004, d304332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31004, d304332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d31005 q = 1) (hb : d300100 q = 1) : d304333 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31005, d304333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31005, d304333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro77709 (p : Pattern) (ha : d31011 p = 1) (hb : d300100 p = 1) : d304339 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31006 q = 1) (hb : d300100 q = 1) : d304334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31006, d304334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77708 q ha hb
    | true =>
      simp only [d31006, d304334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31007 q = 1) (hb : d300100 q = 1) : d304335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31007, d304335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31007, d304335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30916 q = 1) (hb : d300100 q = 1) : d304202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77683 q ha hb
    | true =>
      simp only [d30916, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30917 q = 1) (hb : d300100 q = 1) : d304203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31008 q = 1) (hb : d300100 q = 1) : d304336 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31008, d304336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31008, d304336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31009 q = 1) (hb : d300100 q = 1) : d304337 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31009, d304337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31009, d304337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31010 q = 1) (hb : d300100 q = 1) : d304338 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31010, d304338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31010, d304338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31011 q = 1) (hb : d300100 q = 1) : d304339 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31011, d304339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31011, d304339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77710 (p : Pattern) (ha : d31060 p = 1) (hb : d300100 p = 1) : d304345 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d300100 q = 1) : d304202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77683 q ha hb
    | true =>
      simp only [d30916, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d300100 q = 1) : d304203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31057 q = 1) (hb : d300100 q = 1) : d304342 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31057, d304342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31057, d304342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31058 q = 1) (hb : d300100 q = 1) : d304343 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31058, d304343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31058, d304343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31059 q = 1) (hb : d300100 q = 1) : d304344 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31059, d304344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31059, d304344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31060 q = 1) (hb : d300100 q = 1) : d304345 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31060, d304345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31060, d304345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77711 (p : Pattern) (ha : d245431 p = 1) (hb : d300100 p = 1) : d304351 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30953 q = 1) (hb : d300100 q = 1) : d304297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30953, d304297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77697 q ha hb
    | true =>
      simp only [d30953, d304297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77698 q ha hb
  have h2 (q : Pattern) (ha : d30954 q = 1) (hb : d300100 q = 1) : d304298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30954, d304298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30954, d304298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30955 q = 1) (hb : d300100 q = 1) : d304299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30955, d304299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30955, d304299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30956 q = 1) (hb : d300100 q = 1) : d304300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30956, d304300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30956, d304300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30963 q = 1) (hb : d300100 q = 1) : d304304 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30963, d304304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77699 q ha hb
    | true =>
      simp only [d30963, d304304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77700 q ha hb
  have h6 (q : Pattern) (ha : d30964 q = 1) (hb : d300100 q = 1) : d304305 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30964, d304305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30964, d304305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30965 q = 1) (hb : d300100 q = 1) : d304306 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30965, d304306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30965, d304306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31012 q = 1) (hb : d300100 q = 1) : d304340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31012, d304340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77709 q ha hb
    | true =>
      simp only [d31012, d304340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77685 q ha hb
  have h9 (q : Pattern) (ha : d245427 q = 1) (hb : d300100 q = 1) : d304341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245427, d304341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245427, d304341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d31061 q = 1) (hb : d300100 q = 1) : d304346 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31061, d304346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77710 q ha hb
    | true =>
      simp only [d31061, d304346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31062 q = 1) (hb : d300100 q = 1) : d304347 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31062, d304347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31062, d304347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245428 q = 1) (hb : d300100 q = 1) : d304348 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245428, d304348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245428, d304348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245429 q = 1) (hb : d300100 q = 1) : d304349 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245429, d304349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245429, d304349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245430 q = 1) (hb : d300100 q = 1) : d304350 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245430, d304350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245430, d304350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d245431 q = 1) (hb : d300100 q = 1) : d304351 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245431, d304351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245431, d304351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro77712 (p : Pattern) (ha : d31067 p = 1) (hb : d300100 p = 1) : d304352 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d300100 q = 1) : d304202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77683 q ha hb
    | true =>
      simp only [d30916, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d300100 q = 1) : d304203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30920 q = 1) (hb : d300100 q = 1) : d304091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77684 q ha hb
    | true =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30921 q = 1) (hb : d300100 q = 1) : d304092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30922 q = 1) (hb : d300100 q = 1) : d304204 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30922, d304204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30922, d304204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30923 q = 1) (hb : d300100 q = 1) : d304205 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30923, d304205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30923, d304205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30949 q = 1) (hb : d300100 q = 1) : d304295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30949, d304295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30949, d304295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31067 q = 1) (hb : d300100 q = 1) : d304352 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31067, d304352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31067, d304352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro77713 (p : Pattern) (ha : d31068 p = 1) (hb : d300100 p = 1) : d304214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30920 q = 1) (hb : d300100 q = 1) : d304091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77684 q ha hb
    | true =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30921 q = 1) (hb : d300100 q = 1) : d304092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30926 q = 1) (hb : d300100 q = 1) : d304093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30926, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30926, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30927 q = 1) (hb : d300100 q = 1) : d304094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30927, d304094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30927, d304094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30951 q = 1) (hb : d300100 q = 1) : d304170 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30951, d304170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30951, d304170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31068 q = 1) (hb : d300100 q = 1) : d304214 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31068, d304214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31068, d304214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77714 (p : Pattern) (ha : d31073 p = 1) (hb : d300100 p = 1) : d304357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d300100 q = 1) : d304202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77683 q ha hb
    | true =>
      simp only [d30916, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d300100 q = 1) : d304203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30920 q = 1) (hb : d300100 q = 1) : d304091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77684 q ha hb
    | true =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30921 q = 1) (hb : d300100 q = 1) : d304092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30922 q = 1) (hb : d300100 q = 1) : d304204 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30922, d304204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30922, d304204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30957 q = 1) (hb : d300100 q = 1) : d304301 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30957, d304301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30957, d304301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30958 q = 1) (hb : d300100 q = 1) : d304302 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30958, d304302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30958, d304302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31073 q = 1) (hb : d300100 q = 1) : d304357 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31073, d304357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31073, d304357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro77715 (p : Pattern) (ha : d31074 p = 1) (hb : d300100 p = 1) : d304219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30920 q = 1) (hb : d300100 q = 1) : d304091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77684 q ha hb
    | true =>
      simp only [d30920, d304091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30921 q = 1) (hb : d300100 q = 1) : d304092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d304092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30926 q = 1) (hb : d300100 q = 1) : d304093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30926, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30926, d304093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30960 q = 1) (hb : d300100 q = 1) : d304176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30960, d304176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30960, d304176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30961 q = 1) (hb : d300100 q = 1) : d304177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30961, d304177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30961, d304177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31074 q = 1) (hb : d300100 q = 1) : d304219 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31074, d304219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31074, d304219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77716 (p : Pattern) (ha : d31078 p = 1) (hb : d300100 p = 1) : d304361 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31006 q = 1) (hb : d300100 q = 1) : d304334 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31006, d304334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77708 q ha hb
    | true =>
      simp only [d31006, d304334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31007 q = 1) (hb : d300100 q = 1) : d304335 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31007, d304335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31007, d304335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30916 q = 1) (hb : d300100 q = 1) : d304202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77683 q ha hb
    | true =>
      simp only [d30916, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30917 q = 1) (hb : d300100 q = 1) : d304203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31008 q = 1) (hb : d300100 q = 1) : d304336 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31008, d304336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31008, d304336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31009 q = 1) (hb : d300100 q = 1) : d304337 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31009, d304337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31009, d304337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31010 q = 1) (hb : d300100 q = 1) : d304338 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31010, d304338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31010, d304338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31078 q = 1) (hb : d300100 q = 1) : d304361 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31078, d304361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31078, d304361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro77717 (p : Pattern) (ha : d31084 p = 1) (hb : d300100 p = 1) : d304364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d300100 q = 1) : d304202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77683 q ha hb
    | true =>
      simp only [d30916, d304202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d300100 q = 1) : d304203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d304203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31057 q = 1) (hb : d300100 q = 1) : d304342 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31057, d304342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31057, d304342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31058 q = 1) (hb : d300100 q = 1) : d304343 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31058, d304343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31058, d304343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31059 q = 1) (hb : d300100 q = 1) : d304344 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31059, d304344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31059, d304344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31084 q = 1) (hb : d300100 q = 1) : d304364 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31084, d304364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31084, d304364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77718 (p : Pattern) (ha : d245436 p = 1) (hb : d300100 p = 1) : d304370 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30953 q = 1) (hb : d300100 q = 1) : d304297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30953, d304297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77697 q ha hb
    | true =>
      simp only [d30953, d304297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77698 q ha hb
  have h2 (q : Pattern) (ha : d30954 q = 1) (hb : d300100 q = 1) : d304298 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30954, d304298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30954, d304298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30955 q = 1) (hb : d300100 q = 1) : d304299 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30955, d304299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30955, d304299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30956 q = 1) (hb : d300100 q = 1) : d304300 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30956, d304300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30956, d304300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30963 q = 1) (hb : d300100 q = 1) : d304304 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30963, d304304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77699 q ha hb
    | true =>
      simp only [d30963, d304304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77700 q ha hb
  have h6 (q : Pattern) (ha : d30964 q = 1) (hb : d300100 q = 1) : d304305 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30964, d304305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30964, d304305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30965 q = 1) (hb : d300100 q = 1) : d304306 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30965, d304306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30965, d304306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31012 q = 1) (hb : d300100 q = 1) : d304340 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31012, d304340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77709 q ha hb
    | true =>
      simp only [d31012, d304340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77685 q ha hb
  have h9 (q : Pattern) (ha : d245427 q = 1) (hb : d300100 q = 1) : d304341 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245427, d304341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245427, d304341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d31061 q = 1) (hb : d300100 q = 1) : d304346 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31061, d304346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77710 q ha hb
    | true =>
      simp only [d31061, d304346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31062 q = 1) (hb : d300100 q = 1) : d304347 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31062, d304347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31062, d304347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245428 q = 1) (hb : d300100 q = 1) : d304348 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245428, d304348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245428, d304348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245429 q = 1) (hb : d300100 q = 1) : d304349 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245429, d304349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245429, d304349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245430 q = 1) (hb : d300100 q = 1) : d304350 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245430, d304350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245430, d304350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d31069 q = 1) (hb : d300100 q = 1) : d304353 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31069, d304353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77712 q ha hb
    | true =>
      simp only [d31069, d304353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77713 q ha hb
  have h16 (q : Pattern) (ha : d31070 q = 1) (hb : d300100 q = 1) : d304354 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31070, d304354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31070, d304354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31071 q = 1) (hb : d300100 q = 1) : d304355 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31071, d304355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31071, d304355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31072 q = 1) (hb : d300100 q = 1) : d304356 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31072, d304356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31072, d304356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31075 q = 1) (hb : d300100 q = 1) : d304358 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31075, d304358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77714 q ha hb
    | true =>
      simp only [d31075, d304358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77715 q ha hb
  have h20 (q : Pattern) (ha : d31076 q = 1) (hb : d300100 q = 1) : d304359 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31076, d304359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31076, d304359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d31077 q = 1) (hb : d300100 q = 1) : d304360 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31077, d304360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d31077, d304360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d31079 q = 1) (hb : d300100 q = 1) : d304362 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31079, d304362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77716 q ha hb
    | true =>
      simp only [d31079, d304362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77688 q ha hb
  have h23 (q : Pattern) (ha : d245432 q = 1) (hb : d300100 q = 1) : d304363 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245432, d304363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d245432, d304363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d31085 q = 1) (hb : d300100 q = 1) : d304365 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31085, d304365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77717 q ha hb
    | true =>
      simp only [d31085, d304365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d31086 q = 1) (hb : d300100 q = 1) : d304366 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31086, d304366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d31086, d304366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d245433 q = 1) (hb : d300100 q = 1) : d304367 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245433, d304367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d245433, d304367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d245434 q = 1) (hb : d300100 q = 1) : d304368 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245434, d304368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d245434, d304368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d245435 q = 1) (hb : d300100 q = 1) : d304369 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245435, d304369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d245435, d304369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d245436 q = 1) (hb : d300100 q = 1) : d304370 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245436, d304370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245436, d304370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro77719 (p : Pattern) (ha : d245443 p = 1) (hb : d300100 p = 1) : d304379 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31079 q = 1) (hb : d300100 q = 1) : d304362 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31079, d304362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77716 q ha hb
    | true =>
      simp only [d31079, d304362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77688 q ha hb
  have h2 (q : Pattern) (ha : d245432 q = 1) (hb : d300100 q = 1) : d304363 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245432, d304363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245432, d304363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31085 q = 1) (hb : d300100 q = 1) : d304365 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31085, d304365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77717 q ha hb
    | true =>
      simp only [d31085, d304365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31086 q = 1) (hb : d300100 q = 1) : d304366 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31086, d304366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31086, d304366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245433 q = 1) (hb : d300100 q = 1) : d304367 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245433, d304367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245433, d304367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245441 q = 1) (hb : d300100 q = 1) : d304377 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245441, d304377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245441, d304377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245442 q = 1) (hb : d300100 q = 1) : d304378 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245442, d304378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245442, d304378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245443 q = 1) (hb : d300100 q = 1) : d304379 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245443, d304379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245443, d304379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77720 (p : Pattern) (ha : d31132 p = 1) (hb : d300100 p = 1) : d304397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31118 q = 1) (hb : d300100 q = 1) : d304387 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31118, d304387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31118, d304387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77703 q ha hb
  have h2 (q : Pattern) (ha : d30977 q = 1) (hb : d300100 q = 1) : d304314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30977, d304314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77703 q ha hb
    | true =>
      simp only [d30977, d304314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31119 q = 1) (hb : d300100 q = 1) : d304388 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31119, d304388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31119, d304388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30978 q = 1) (hb : d300100 q = 1) : d304315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30978, d304315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30978, d304315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31120 q = 1) (hb : d300100 q = 1) : d304389 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31120, d304389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31120, d304389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31121 q = 1) (hb : d300100 q = 1) : d304390 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31121, d304390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31121, d304390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31122 q = 1) (hb : d300100 q = 1) : d304244 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31122, d304244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31122, d304244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77704 q ha hb
  have h8 (q : Pattern) (ha : d30982 q = 1) (hb : d300100 q = 1) : d304190 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30982, d304190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77704 q ha hb
    | true =>
      simp only [d30982, d304190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31123 q = 1) (hb : d300100 q = 1) : d304245 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31123, d304245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31123, d304245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30983 q = 1) (hb : d300100 q = 1) : d304191 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30983, d304191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30983, d304191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31124 q = 1) (hb : d300100 q = 1) : d304246 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31124, d304246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31124, d304246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31125 q = 1) (hb : d300100 q = 1) : d304247 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31125, d304247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31125, d304247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31126 q = 1) (hb : d300100 q = 1) : d304391 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31126, d304391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31126, d304391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31127 q = 1) (hb : d300100 q = 1) : d304392 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31127, d304392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31127, d304392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77705 q ha hb
  have h15 (q : Pattern) (ha : d30990 q = 1) (hb : d300100 q = 1) : d304322 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30990, d304322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77705 q ha hb
    | true =>
      simp only [d30990, d304322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d31128 q = 1) (hb : d300100 q = 1) : d304393 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31128, d304393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31128, d304393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d30991 q = 1) (hb : d300100 q = 1) : d304323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30991, d304323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d30991, d304323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31129 q = 1) (hb : d300100 q = 1) : d304394 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31129, d304394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31129, d304394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31130 q = 1) (hb : d300100 q = 1) : d304395 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31130, d304395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d31130, d304395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d30852 q = 1) (hb : d300100 q = 1) : d304120 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30852, d304120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30852, d304120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77664 q ha hb
  have h21 (q : Pattern) (ha : d30759 q = 1) (hb : d300100 q = 1) : d304079 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30759, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77664 q ha hb
    | true =>
      simp only [d30759, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d30853 q = 1) (hb : d300100 q = 1) : d304121 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30853, d304121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d30853, d304121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d30760 q = 1) (hb : d300100 q = 1) : d304080 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30760, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d30760, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d30854 q = 1) (hb : d300100 q = 1) : d304122 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30854, d304122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d30854, d304122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d30855 q = 1) (hb : d300100 q = 1) : d304123 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30855, d304123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d30855, d304123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d31131 q = 1) (hb : d300100 q = 1) : d304396 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31131, d304396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d31131, d304396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d31132 q = 1) (hb : d300100 q = 1) : d304397 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31132, d304397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31132, d304397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro77721 (p : Pattern) (ha : d31136 p = 1) (hb : d300100 p = 1) : d304125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30852 q = 1) (hb : d300100 q = 1) : d304120 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30852, d304120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30852, d304120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77664 q ha hb
  have h2 (q : Pattern) (ha : d30759 q = 1) (hb : d300100 q = 1) : d304079 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30759, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77664 q ha hb
    | true =>
      simp only [d30759, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30853 q = 1) (hb : d300100 q = 1) : d304121 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30853, d304121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30853, d304121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30760 q = 1) (hb : d300100 q = 1) : d304080 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30760, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30760, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30854 q = 1) (hb : d300100 q = 1) : d304122 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30854, d304122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30854, d304122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30855 q = 1) (hb : d300100 q = 1) : d304123 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30855, d304123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30855, d304123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77621 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77621 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30856 q = 1) (hb : d300100 q = 1) : d304124 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30856, d304124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30856, d304124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d31136 q = 1) (hb : d300100 q = 1) : d304125 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31136, d304125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31136, d304125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro77722 (p : Pattern) (ha : d31142 p = 1) (hb : d300100 p = 1) : d304403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31133 q = 1) (hb : d300100 q = 1) : d304398 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31133, d304398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77720 q ha hb
    | true =>
      simp only [d31133, d304398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77676 q ha hb
  have h2 (q : Pattern) (ha : d31134 q = 1) (hb : d300100 q = 1) : d304399 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31134, d304399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31134, d304399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31135 q = 1) (hb : d300100 q = 1) : d304400 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31135, d304400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31135, d304400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31137 q = 1) (hb : d300100 q = 1) : d304250 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31137, d304250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77676 q ha hb
    | true =>
      simp only [d31137, d304250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77721 q ha hb
  have h5 (q : Pattern) (ha : d31138 q = 1) (hb : d300100 q = 1) : d304251 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31138, d304251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31138, d304251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31139 q = 1) (hb : d300100 q = 1) : d304252 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31139, d304252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31139, d304252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31140 q = 1) (hb : d300100 q = 1) : d304401 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31140, d304401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31140, d304401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30858 q = 1) (hb : d300100 q = 1) : d304250 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30858, d304250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77676 q ha hb
    | true =>
      simp only [d30858, d304250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77650 q ha hb
  have h9 (q : Pattern) (ha : d30859 q = 1) (hb : d300100 q = 1) : d304251 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30859, d304251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30859, d304251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30860 q = 1) (hb : d300100 q = 1) : d304252 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30860, d304252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30860, d304252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30688 q = 1) (hb : d300100 q = 1) : d304126 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30688, d304126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77650 q ha hb
    | true =>
      simp only [d30688, d304126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77629 q ha hb
  have h12 (q : Pattern) (ha : d30689 q = 1) (hb : d300100 q = 1) : d304127 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30689, d304127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30689, d304127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30690 q = 1) (hb : d300100 q = 1) : d304128 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30690, d304128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30690, d304128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d30861 q = 1) (hb : d300100 q = 1) : d304253 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30861, d304253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30861, d304253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d31141 q = 1) (hb : d300100 q = 1) : d304402 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31141, d304402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31141, d304402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d31142 q = 1) (hb : d300100 q = 1) : d304403 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31142, d304403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31142, d304403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro77723 (p : Pattern) (ha : d31147 p = 1) (hb : d300100 p = 1) : d304255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30858 q = 1) (hb : d300100 q = 1) : d304250 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30858, d304250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77676 q ha hb
    | true =>
      simp only [d30858, d304250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77650 q ha hb
  have h2 (q : Pattern) (ha : d30859 q = 1) (hb : d300100 q = 1) : d304251 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30859, d304251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30859, d304251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30860 q = 1) (hb : d300100 q = 1) : d304252 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30860, d304252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30860, d304252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30688 q = 1) (hb : d300100 q = 1) : d304126 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30688, d304126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77650 q ha hb
    | true =>
      simp only [d30688, d304126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77629 q ha hb
  have h5 (q : Pattern) (ha : d30689 q = 1) (hb : d300100 q = 1) : d304127 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30689, d304127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30689, d304127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30690 q = 1) (hb : d300100 q = 1) : d304128 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30690, d304128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30690, d304128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30861 q = 1) (hb : d300100 q = 1) : d304253 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30861, d304253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30861, d304253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31145 q = 1) (hb : d300100 q = 1) : d304129 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31145, d304129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31145, d304129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31146 q = 1) (hb : d300100 q = 1) : d304254 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31146, d304254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31146, d304254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31147 q = 1) (hb : d300100 q = 1) : d304255 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31147, d304255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31147, d304255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro77724 (p : Pattern) (ha : d31153 p = 1) (hb : d300100 p = 1) : d304409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31143 q = 1) (hb : d300100 q = 1) : d304404 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31143, d304404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77722 q ha hb
    | true =>
      simp only [d31143, d304404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31144 q = 1) (hb : d300100 q = 1) : d304405 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31144, d304405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31144, d304405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31148 q = 1) (hb : d300100 q = 1) : d304256 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31148, d304256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77723 q ha hb
    | true =>
      simp only [d31148, d304256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31149 q = 1) (hb : d300100 q = 1) : d304257 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31149, d304257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31149, d304257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31150 q = 1) (hb : d300100 q = 1) : d304406 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31150, d304406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31150, d304406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31151 q = 1) (hb : d300100 q = 1) : d304407 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31151, d304407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31151, d304407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31152 q = 1) (hb : d300100 q = 1) : d304408 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31152, d304408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31152, d304408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31153 q = 1) (hb : d300100 q = 1) : d304409 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31153, d304409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31153, d304409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro77725 (p : Pattern) (ha : d31161 p = 1) (hb : d300100 p = 1) : d304261 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31148 q = 1) (hb : d300100 q = 1) : d304256 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31148, d304256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77723 q ha hb
    | true =>
      simp only [d31148, d304256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31149 q = 1) (hb : d300100 q = 1) : d304257 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31149, d304257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31149, d304257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31156 q = 1) (hb : d300100 q = 1) : d304132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31156, d304132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77694 q ha hb
    | true =>
      simp only [d31156, d304132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31157 q = 1) (hb : d300100 q = 1) : d304133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31157, d304133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31157, d304133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31158 q = 1) (hb : d300100 q = 1) : d304258 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31158, d304258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31158, d304258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31159 q = 1) (hb : d300100 q = 1) : d304259 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31159, d304259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31159, d304259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31160 q = 1) (hb : d300100 q = 1) : d304260 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31160, d304260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31160, d304260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31161 q = 1) (hb : d300100 q = 1) : d304261 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31161, d304261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31161, d304261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro77726 (p : Pattern) (ha : d31200 p = 1) (hb : d300100 p = 1) : d304415 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31148 q = 1) (hb : d300100 q = 1) : d304256 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31148, d304256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77723 q ha hb
    | true =>
      simp only [d31148, d304256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31149 q = 1) (hb : d300100 q = 1) : d304257 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31149, d304257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31149, d304257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31197 q = 1) (hb : d300100 q = 1) : d304412 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31197, d304412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31197, d304412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31198 q = 1) (hb : d300100 q = 1) : d304413 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31198, d304413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31198, d304413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31199 q = 1) (hb : d300100 q = 1) : d304414 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31199, d304414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31199, d304414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31200 q = 1) (hb : d300100 q = 1) : d304415 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31200, d304415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31200, d304415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77727 (p : Pattern) (ha : d245453 p = 1) (hb : d300100 p = 1) : d304421 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31162 q = 1) (hb : d300100 q = 1) : d304410 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31162, d304410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77724 q ha hb
    | true =>
      simp only [d31162, d304410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77725 q ha hb
  have h2 (q : Pattern) (ha : d245449 q = 1) (hb : d300100 q = 1) : d304411 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245449, d304411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245449, d304411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31201 q = 1) (hb : d300100 q = 1) : d304416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31201, d304416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77726 q ha hb
    | true =>
      simp only [d31201, d304416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31202 q = 1) (hb : d300100 q = 1) : d304417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31202, d304417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31202, d304417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245450 q = 1) (hb : d300100 q = 1) : d304418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245450, d304418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245450, d304418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245451 q = 1) (hb : d300100 q = 1) : d304419 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245451, d304419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245451, d304419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245452 q = 1) (hb : d300100 q = 1) : d304420 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245452, d304420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245452, d304420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245453 q = 1) (hb : d300100 q = 1) : d304421 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245453, d304421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245453, d304421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77728 (p : Pattern) (ha : d245459 p = 1) (hb : d300100 p = 1) : d304433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30936 q = 1) (hb : d300100 q = 1) : d304285 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30936, d304285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30936, d304285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77687 q ha hb
  have h2 (q : Pattern) (ha : d30937 q = 1) (hb : d300100 q = 1) : d304286 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d30937, d304286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30937, d304286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30946 q = 1) (hb : d300100 q = 1) : d304292 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30946, d304292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77687 q ha hb
    | true =>
      simp only [d30946, d304292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77690 q ha hb
  have h4 (q : Pattern) (ha : d30947 q = 1) (hb : d300100 q = 1) : d304293 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d30947, d304293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30947, d304293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30948 q = 1) (hb : d300100 q = 1) : d304294 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d30948, d304294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30948, d304294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245437 q = 1) (hb : d300100 q = 1) : d304371 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245437, d304371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77711 q ha hb
    | true =>
      simp only [d245437, d304371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77718 q ha hb
  have h7 (q : Pattern) (ha : d31104 q = 1) (hb : d300100 q = 1) : d304373 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31104, d304373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77691 q ha hb
    | true =>
      simp only [d31104, d304373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77692 q ha hb
  have h8 (q : Pattern) (ha : d245438 q = 1) (hb : d300100 q = 1) : d304374 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245438, d304374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245438, d304374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245439 q = 1) (hb : d300100 q = 1) : d304375 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245439, d304375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245439, d304375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d245440 q = 1) (hb : d300100 q = 1) : d304376 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245440, d304376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245440, d304376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245444 q = 1) (hb : d300100 q = 1) : d304380 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245444, d304380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245444, d304380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77719 q ha hb
  have h12 (q : Pattern) (ha : d31113 q = 1) (hb : d300100 q = 1) : d304382 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31113, d304382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31113, d304382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77693 q ha hb
  have h13 (q : Pattern) (ha : d245445 q = 1) (hb : d300100 q = 1) : d304383 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245445, d304383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245445, d304383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245446 q = 1) (hb : d300100 q = 1) : d304384 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245446, d304384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245446, d304384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245447 q = 1) (hb : d300100 q = 1) : d304385 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245447, d304385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245447, d304385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d245448 q = 1) (hb : d300100 q = 1) : d304386 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245448, d304386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245448, d304386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245454 q = 1) (hb : d300100 q = 1) : d304422 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245454, d304422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245454, d304422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77727 q ha hb
  have h18 (q : Pattern) (ha : d31218 q = 1) (hb : d300100 q = 1) : d304428 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31218, d304428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31218, d304428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77696 q ha hb
  have h19 (q : Pattern) (ha : d245455 q = 1) (hb : d300100 q = 1) : d304429 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245455, d304429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245455, d304429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d245456 q = 1) (hb : d300100 q = 1) : d304430 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245456, d304430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d245456, d304430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d245457 q = 1) (hb : d300100 q = 1) : d304431 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245457, d304431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d245457, d304431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d245458 q = 1) (hb : d300100 q = 1) : d304432 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245458, d304432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d245458, d304432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d245459 q = 1) (hb : d300100 q = 1) : d304433 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245459, d304433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245459, d304433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro77729 (p : Pattern) (ha : d245465 p = 1) (hb : d300100 p = 1) : d304439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245460 q = 1) (hb : d300100 q = 1) : d304434 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245460, d304434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245460, d304434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77728 q ha hb
  have h2 (q : Pattern) (ha : d245461 q = 1) (hb : d300100 q = 1) : d304435 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245461, d304435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245461, d304435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245462 q = 1) (hb : d300100 q = 1) : d304436 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245462, d304436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245462, d304436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245463 q = 1) (hb : d300100 q = 1) : d304437 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245463, d304437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245463, d304437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245464 q = 1) (hb : d300100 q = 1) : d304438 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245464, d304438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245464, d304438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245465 q = 1) (hb : d300100 q = 1) : d304439 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245465, d304439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245465, d304439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77730 (p : Pattern) (ha : d31231 p = 1) (hb : d300100 p = 1) : d304078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25433 q = 1) (hb : d300100 q = 1) : d304073 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d25433, d304073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77639 q ha hb
    | true =>
      simp only [d25433, d304073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25434 q = 1) (hb : d300100 q = 1) : d304074 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d25434, d304074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25434, d304074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77620 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30635 q = 1) (hb : d300100 q = 1) : d304075 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d30635, d304075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30635, d304075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30636 q = 1) (hb : d300100 q = 1) : d304076 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30636, d304076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30636, d304076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30637 q = 1) (hb : d300100 q = 1) : d304077 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30637, d304077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30637, d304077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31231 q = 1) (hb : d300100 q = 1) : d304078 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31231, d304078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31231, d304078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro77731 (p : Pattern) (ha : d31237 p = 1) (hb : d300100 p = 1) : d304327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30977 q = 1) (hb : d300100 q = 1) : d304314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30977, d304314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77703 q ha hb
    | true =>
      simp only [d30977, d304314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30978 q = 1) (hb : d300100 q = 1) : d304315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30978, d304315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30978, d304315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30979 q = 1) (hb : d300100 q = 1) : d304316 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30979, d304316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30979, d304316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30980 q = 1) (hb : d300100 q = 1) : d304317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30980, d304317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30980, d304317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30982 q = 1) (hb : d300100 q = 1) : d304190 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30982, d304190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77704 q ha hb
    | true =>
      simp only [d30982, d304190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30983 q = 1) (hb : d300100 q = 1) : d304191 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30983, d304191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30983, d304191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30984 q = 1) (hb : d300100 q = 1) : d304192 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30984, d304192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30984, d304192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30985 q = 1) (hb : d300100 q = 1) : d304193 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30985, d304193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30985, d304193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30986 q = 1) (hb : d300100 q = 1) : d304318 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30986, d304318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30986, d304318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30990 q = 1) (hb : d300100 q = 1) : d304322 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30990, d304322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77705 q ha hb
    | true =>
      simp only [d30990, d304322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30991 q = 1) (hb : d300100 q = 1) : d304323 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30991, d304323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30991, d304323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d30992 q = 1) (hb : d300100 q = 1) : d304324 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30992, d304324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30992, d304324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30993 q = 1) (hb : d300100 q = 1) : d304325 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30993, d304325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30993, d304325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d31232 q = 1) (hb : d300100 q = 1) : d304079 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31232, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77730 q ha hb
    | true =>
      simp only [d31232, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d31233 q = 1) (hb : d300100 q = 1) : d304080 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31233, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31233, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d31234 q = 1) (hb : d300100 q = 1) : d304081 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31234, d304081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31234, d304081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31235 q = 1) (hb : d300100 q = 1) : d304082 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31235, d304082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31235, d304082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31236 q = 1) (hb : d300100 q = 1) : d304326 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31236, d304326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31236, d304326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31237 q = 1) (hb : d300100 q = 1) : d304327 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31237, d304327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31237, d304327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro77732 (p : Pattern) (ha : d31240 p = 1) (hb : d300100 p = 1) : d304195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30751 q = 1) (hb : d300100 q = 1) : d304190 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30751, d304190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77663 q ha hb
    | true =>
      simp only [d30751, d304190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30752 q = 1) (hb : d300100 q = 1) : d304191 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30752, d304191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30752, d304191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30753 q = 1) (hb : d300100 q = 1) : d304192 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30753, d304192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30753, d304192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30754 q = 1) (hb : d300100 q = 1) : d304193 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30754, d304193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30754, d304193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31232 q = 1) (hb : d300100 q = 1) : d304079 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31232, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77730 q ha hb
    | true =>
      simp only [d31232, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31233 q = 1) (hb : d300100 q = 1) : d304080 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31233, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31233, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31234 q = 1) (hb : d300100 q = 1) : d304081 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31234, d304081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31234, d304081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31235 q = 1) (hb : d300100 q = 1) : d304082 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31235, d304082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31235, d304082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31238 q = 1) (hb : d300100 q = 1) : d304194 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31238, d304194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31238, d304194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31239 q = 1) (hb : d300100 q = 1) : d304083 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31239, d304083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31239, d304083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31240 q = 1) (hb : d300100 q = 1) : d304195 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31240, d304195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31240, d304195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro77733 (p : Pattern) (ha : d31244 p = 1) (hb : d300100 p = 1) : d304084 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31232 q = 1) (hb : d300100 q = 1) : d304079 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31232, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77730 q ha hb
    | true =>
      simp only [d31232, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31233 q = 1) (hb : d300100 q = 1) : d304080 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31233, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31233, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31234 q = 1) (hb : d300100 q = 1) : d304081 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31234, d304081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31234, d304081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31235 q = 1) (hb : d300100 q = 1) : d304082 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31235, d304082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31235, d304082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31239 q = 1) (hb : d300100 q = 1) : d304083 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31239, d304083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31239, d304083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31244 q = 1) (hb : d300100 q = 1) : d304084 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31244, d304084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31244, d304084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77734 (p : Pattern) (ha : d31251 p = 1) (hb : d300100 p = 1) : d304443 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31241 q = 1) (hb : d300100 q = 1) : d304328 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31241, d304328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77731 q ha hb
    | true =>
      simp only [d31241, d304328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77732 q ha hb
  have h2 (q : Pattern) (ha : d31242 q = 1) (hb : d300100 q = 1) : d304329 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31242, d304329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31242, d304329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31243 q = 1) (hb : d300100 q = 1) : d304330 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31243, d304330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31243, d304330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31245 q = 1) (hb : d300100 q = 1) : d304196 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31245, d304196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77732 q ha hb
    | true =>
      simp only [d31245, d304196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77733 q ha hb
  have h5 (q : Pattern) (ha : d31246 q = 1) (hb : d300100 q = 1) : d304197 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31246, d304197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31246, d304197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31247 q = 1) (hb : d300100 q = 1) : d304198 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31247, d304198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31247, d304198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31248 q = 1) (hb : d300100 q = 1) : d304331 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31248, d304331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31248, d304331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31249 q = 1) (hb : d300100 q = 1) : d304441 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31249, d304441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31249, d304441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31250 q = 1) (hb : d300100 q = 1) : d304442 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31250, d304442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31250, d304442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31251 q = 1) (hb : d300100 q = 1) : d304443 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31251, d304443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31251, d304443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro77735 (p : Pattern) (ha : d31255 p = 1) (hb : d300100 p = 1) : d304447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31245 q = 1) (hb : d300100 q = 1) : d304196 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31245, d304196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77732 q ha hb
    | true =>
      simp only [d31245, d304196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77733 q ha hb
  have h2 (q : Pattern) (ha : d31246 q = 1) (hb : d300100 q = 1) : d304197 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31246, d304197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31246, d304197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31247 q = 1) (hb : d300100 q = 1) : d304198 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31247, d304198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31247, d304198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31249 q = 1) (hb : d300100 q = 1) : d304441 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31249, d304441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31249, d304441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31254 q = 1) (hb : d300100 q = 1) : d304446 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31254, d304446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31254, d304446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31255 q = 1) (hb : d300100 q = 1) : d304447 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31255, d304447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31255, d304447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77736 (p : Pattern) (ha : d31261 p = 1) (hb : d300100 p = 1) : d304453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31252 q = 1) (hb : d300100 q = 1) : d304444 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31252, d304444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77734 q ha hb
    | true =>
      simp only [d31252, d304444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31253 q = 1) (hb : d300100 q = 1) : d304445 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31253, d304445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31253, d304445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31256 q = 1) (hb : d300100 q = 1) : d304448 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d304448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77735 q ha hb
    | true =>
      simp only [d31256, d304448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31257 q = 1) (hb : d300100 q = 1) : d304449 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d304449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d304449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31258 q = 1) (hb : d300100 q = 1) : d304450 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31258, d304450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31258, d304450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31259 q = 1) (hb : d300100 q = 1) : d304451 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31259, d304451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31259, d304451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31260 q = 1) (hb : d300100 q = 1) : d304452 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31260, d304452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31260, d304452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31261 q = 1) (hb : d300100 q = 1) : d304453 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31261, d304453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31261, d304453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro77737 (p : Pattern) (ha : d31265 p = 1) (hb : d300100 p = 1) : d304457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31256 q = 1) (hb : d300100 q = 1) : d304448 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d304448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77735 q ha hb
    | true =>
      simp only [d31256, d304448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31257 q = 1) (hb : d300100 q = 1) : d304449 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d304449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d304449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31262 q = 1) (hb : d300100 q = 1) : d304454 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31262, d304454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31262, d304454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31263 q = 1) (hb : d300100 q = 1) : d304455 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31263, d304455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31263, d304455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31264 q = 1) (hb : d300100 q = 1) : d304456 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31264, d304456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31264, d304456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31265 q = 1) (hb : d300100 q = 1) : d304457 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31265, d304457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31265, d304457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77738 (p : Pattern) (ha : d31271 p = 1) (hb : d300100 p = 1) : d304463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31266 q = 1) (hb : d300100 q = 1) : d304458 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31266, d304458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77736 q ha hb
    | true =>
      simp only [d31266, d304458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77737 q ha hb
  have h2 (q : Pattern) (ha : d31267 q = 1) (hb : d300100 q = 1) : d304459 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31267, d304459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31267, d304459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31268 q = 1) (hb : d300100 q = 1) : d304460 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31268, d304460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31268, d304460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31269 q = 1) (hb : d300100 q = 1) : d304461 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31269, d304461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31269, d304461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31270 q = 1) (hb : d300100 q = 1) : d304462 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31270, d304462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31270, d304462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31271 q = 1) (hb : d300100 q = 1) : d304463 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31271, d304463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31271, d304463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77739 (p : Pattern) (ha : d31274 p = 1) (hb : d300100 p = 1) : d304466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31252 q = 1) (hb : d300100 q = 1) : d304444 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31252, d304444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77734 q ha hb
    | true =>
      simp only [d31252, d304444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31253 q = 1) (hb : d300100 q = 1) : d304445 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31253, d304445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31253, d304445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31256 q = 1) (hb : d300100 q = 1) : d304448 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d304448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77735 q ha hb
    | true =>
      simp only [d31256, d304448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31257 q = 1) (hb : d300100 q = 1) : d304449 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d304449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d304449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31258 q = 1) (hb : d300100 q = 1) : d304450 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31258, d304450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31258, d304450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31259 q = 1) (hb : d300100 q = 1) : d304451 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31259, d304451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31259, d304451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31260 q = 1) (hb : d300100 q = 1) : d304452 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31260, d304452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31260, d304452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31274 q = 1) (hb : d300100 q = 1) : d304466 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31274, d304466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31274, d304466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro77740 (p : Pattern) (ha : d31275 p = 1) (hb : d300100 p = 1) : d304467 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31256 q = 1) (hb : d300100 q = 1) : d304448 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d304448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77735 q ha hb
    | true =>
      simp only [d31256, d304448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31257 q = 1) (hb : d300100 q = 1) : d304449 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d304449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d304449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31262 q = 1) (hb : d300100 q = 1) : d304454 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31262, d304454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31262, d304454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31263 q = 1) (hb : d300100 q = 1) : d304455 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31263, d304455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31263, d304455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31264 q = 1) (hb : d300100 q = 1) : d304456 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31264, d304456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31264, d304456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31275 q = 1) (hb : d300100 q = 1) : d304467 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31275, d304467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31275, d304467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77741 (p : Pattern) (ha : d31281 p = 1) (hb : d300100 p = 1) : d304473 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31266 q = 1) (hb : d300100 q = 1) : d304458 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31266, d304458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77736 q ha hb
    | true =>
      simp only [d31266, d304458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77737 q ha hb
  have h2 (q : Pattern) (ha : d31267 q = 1) (hb : d300100 q = 1) : d304459 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31267, d304459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31267, d304459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31268 q = 1) (hb : d300100 q = 1) : d304460 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31268, d304460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31268, d304460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31269 q = 1) (hb : d300100 q = 1) : d304461 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31269, d304461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31269, d304461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31270 q = 1) (hb : d300100 q = 1) : d304462 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31270, d304462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31270, d304462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31276 q = 1) (hb : d300100 q = 1) : d304468 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31276, d304468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77739 q ha hb
    | true =>
      simp only [d31276, d304468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77740 q ha hb
  have h7 (q : Pattern) (ha : d31277 q = 1) (hb : d300100 q = 1) : d304469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31277, d304469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31277, d304469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31278 q = 1) (hb : d300100 q = 1) : d304470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31278, d304470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31278, d304470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31279 q = 1) (hb : d300100 q = 1) : d304471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31279, d304471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31279, d304471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31280 q = 1) (hb : d300100 q = 1) : d304472 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31280, d304472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31280, d304472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31281 q = 1) (hb : d300100 q = 1) : d304473 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31281, d304473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31281, d304473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro77742 (p : Pattern) (ha : d31454 p = 1) (hb : d300100 p = 1) : d304580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31266 q = 1) (hb : d300100 q = 1) : d304458 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31266, d304458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77736 q ha hb
    | true =>
      simp only [d31266, d304458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77737 q ha hb
  have h2 (q : Pattern) (ha : d31267 q = 1) (hb : d300100 q = 1) : d304459 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31267, d304459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31267, d304459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31268 q = 1) (hb : d300100 q = 1) : d304460 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31268, d304460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31268, d304460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31269 q = 1) (hb : d300100 q = 1) : d304461 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31269, d304461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31269, d304461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31270 q = 1) (hb : d300100 q = 1) : d304462 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31270, d304462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31270, d304462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31449 q = 1) (hb : d300100 q = 1) : d304575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31449, d304575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77737 q ha hb
    | true =>
      simp only [d31449, d304575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31450 q = 1) (hb : d300100 q = 1) : d304576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31450, d304576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31450, d304576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31451 q = 1) (hb : d300100 q = 1) : d304577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31451, d304577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31451, d304577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31452 q = 1) (hb : d300100 q = 1) : d304578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31452, d304578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31452, d304578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31453 q = 1) (hb : d300100 q = 1) : d304579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31453, d304579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31453, d304579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31454 q = 1) (hb : d300100 q = 1) : d304580 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31454, d304580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31454, d304580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro77743 (p : Pattern) (ha : d31460 p = 1) (hb : d300100 p = 1) : d304586 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31449 q = 1) (hb : d300100 q = 1) : d304575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31449, d304575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77737 q ha hb
    | true =>
      simp only [d31449, d304575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31450 q = 1) (hb : d300100 q = 1) : d304576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31450, d304576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31450, d304576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31451 q = 1) (hb : d300100 q = 1) : d304577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31451, d304577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31451, d304577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31452 q = 1) (hb : d300100 q = 1) : d304578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31452, d304578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31452, d304578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31453 q = 1) (hb : d300100 q = 1) : d304579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31453, d304579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31453, d304579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31455 q = 1) (hb : d300100 q = 1) : d304581 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31455, d304581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77740 q ha hb
    | true =>
      simp only [d31455, d304581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31456 q = 1) (hb : d300100 q = 1) : d304582 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31456, d304582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31456, d304582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31457 q = 1) (hb : d300100 q = 1) : d304583 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31457, d304583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31457, d304583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31458 q = 1) (hb : d300100 q = 1) : d304584 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31458, d304584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31458, d304584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31459 q = 1) (hb : d300100 q = 1) : d304585 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31459, d304585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31459, d304585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31460 q = 1) (hb : d300100 q = 1) : d304586 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31460, d304586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31460, d304586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro77744 (p : Pattern) (ha : d31469 p = 1) (hb : d300100 p = 1) : d304595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31455 q = 1) (hb : d300100 q = 1) : d304581 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31455, d304581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77740 q ha hb
    | true =>
      simp only [d31455, d304581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31456 q = 1) (hb : d300100 q = 1) : d304582 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31456, d304582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31456, d304582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31457 q = 1) (hb : d300100 q = 1) : d304583 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31457, d304583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31457, d304583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31458 q = 1) (hb : d300100 q = 1) : d304584 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31458, d304584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31458, d304584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31459 q = 1) (hb : d300100 q = 1) : d304585 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31459, d304585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31459, d304585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31469 q = 1) (hb : d300100 q = 1) : d304595 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31469, d304595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31469, d304595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro77745 (p : Pattern) (ha : d31506 p = 1) (hb : d300100 p = 1) : d304249 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30847 q = 1) (hb : d300100 q = 1) : d304244 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30847, d304244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30847, d304244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77663 q ha hb
  have h2 (q : Pattern) (ha : d30751 q = 1) (hb : d300100 q = 1) : d304190 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30751, d304190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77663 q ha hb
    | true =>
      simp only [d30751, d304190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30848 q = 1) (hb : d300100 q = 1) : d304245 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30848, d304245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30848, d304245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30752 q = 1) (hb : d300100 q = 1) : d304191 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30752, d304191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30752, d304191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30849 q = 1) (hb : d300100 q = 1) : d304246 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30849, d304246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30849, d304246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30850 q = 1) (hb : d300100 q = 1) : d304247 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30850, d304247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30850, d304247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31490 q = 1) (hb : d300100 q = 1) : d304120 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31490, d304120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31490, d304120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77730 q ha hb
  have h8 (q : Pattern) (ha : d31232 q = 1) (hb : d300100 q = 1) : d304079 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31232, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77730 q ha hb
    | true =>
      simp only [d31232, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31491 q = 1) (hb : d300100 q = 1) : d304121 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31491, d304121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31491, d304121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31233 q = 1) (hb : d300100 q = 1) : d304080 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31233, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31233, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31492 q = 1) (hb : d300100 q = 1) : d304122 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31492, d304122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31492, d304122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31493 q = 1) (hb : d300100 q = 1) : d304123 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31493, d304123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31493, d304123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31505 q = 1) (hb : d300100 q = 1) : d304248 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31505, d304248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31505, d304248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31499 q = 1) (hb : d300100 q = 1) : d304124 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31499, d304124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31499, d304124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d31506 q = 1) (hb : d300100 q = 1) : d304249 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31506, d304249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31506, d304249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro77746 (p : Pattern) (ha : d31510 p = 1) (hb : d300100 p = 1) : d304125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31490 q = 1) (hb : d300100 q = 1) : d304120 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31490, d304120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31490, d304120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77730 q ha hb
  have h2 (q : Pattern) (ha : d31232 q = 1) (hb : d300100 q = 1) : d304079 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31232, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77730 q ha hb
    | true =>
      simp only [d31232, d304079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31491 q = 1) (hb : d300100 q = 1) : d304121 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31491, d304121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31491, d304121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31233 q = 1) (hb : d300100 q = 1) : d304080 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31233, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31233, d304080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31492 q = 1) (hb : d300100 q = 1) : d304122 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31492, d304122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31492, d304122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31493 q = 1) (hb : d300100 q = 1) : d304123 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31493, d304123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31493, d304123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31499 q = 1) (hb : d300100 q = 1) : d304124 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31499, d304124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31499, d304124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31510 q = 1) (hb : d300100 q = 1) : d304125 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31510, d304125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31510, d304125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro77747 (p : Pattern) (ha : d31529 p = 1) (hb : d300100 p = 1) : d304638 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31511 q = 1) (hb : d300100 q = 1) : d304250 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31511, d304250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77745 q ha hb
    | true =>
      simp only [d31511, d304250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77746 q ha hb
  have h2 (q : Pattern) (ha : d31512 q = 1) (hb : d300100 q = 1) : d304251 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31512, d304251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31512, d304251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31513 q = 1) (hb : d300100 q = 1) : d304252 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31513, d304252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31513, d304252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31519 q = 1) (hb : d300100 q = 1) : d304628 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31519, d304628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31519, d304628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31528 q = 1) (hb : d300100 q = 1) : d304637 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31528, d304637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31528, d304637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31529 q = 1) (hb : d300100 q = 1) : d304638 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31529, d304638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31529, d304638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77748 (p : Pattern) (ha : d31600 p = 1) (hb : d300100 p = 1) : d304661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31530 q = 1) (hb : d300100 q = 1) : d304639 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31530, d304639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77747 q ha hb
    | true =>
      simp only [d31530, d304639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31531 q = 1) (hb : d300100 q = 1) : d304640 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31531, d304640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31531, d304640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31597 q = 1) (hb : d300100 q = 1) : d304658 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31597, d304658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31597, d304658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31598 q = 1) (hb : d300100 q = 1) : d304659 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31598, d304659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31598, d304659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31599 q = 1) (hb : d300100 q = 1) : d304660 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31599, d304660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31599, d304660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31600 q = 1) (hb : d300100 q = 1) : d304661 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31600, d304661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31600, d304661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro77749 (p : Pattern) (ha : d31606 p = 1) (hb : d300100 p = 1) : d304667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31601 q = 1) (hb : d300100 q = 1) : d304662 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31601, d304662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77748 q ha hb
    | true =>
      simp only [d31601, d304662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31602 q = 1) (hb : d300100 q = 1) : d304663 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31602, d304663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31602, d304663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31603 q = 1) (hb : d300100 q = 1) : d304664 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31603, d304664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31603, d304664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31604 q = 1) (hb : d300100 q = 1) : d304665 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31604, d304665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31604, d304665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31605 q = 1) (hb : d300100 q = 1) : d304666 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31605, d304666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31605, d304666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31606 q = 1) (hb : d300100 q = 1) : d304667 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31606, d304667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31606, d304667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
