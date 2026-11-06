import NetHack.Soko22Hazard87.AndIntroBlocks0360
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro90250 (p : Pattern) (ha : d270933 p = 1) (hb : d300100 p = 1) : d330911 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37070 q = 1) (hb : d300100 q = 1) : d330187 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d37070, d330187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89748 q ha hb
    | true =>
      simp only [d37070, d330187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89749 q ha hb
  have h2 (q : Pattern) (ha : d37071 q = 1) (hb : d300100 q = 1) : d330188 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37071, d330188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37071, d330188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37072 q = 1) (hb : d300100 q = 1) : d330189 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37072, d330189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d37072, d330189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d37073 q = 1) (hb : d300100 q = 1) : d330190 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37073, d330190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37073, d330190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d37074 q = 1) (hb : d300100 q = 1) : d330191 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37074, d330191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37074, d330191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270933 q = 1) (hb : d300100 q = 1) : d330911 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270933, d330911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270933, d330911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90251 (p : Pattern) (ha : d270944 p = 1) (hb : d300100 p = 1) : d330922 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270939 q = 1) (hb : d300100 q = 1) : d330917 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d270939, d330917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89789 q ha hb
    | true =>
      simp only [d270939, d330917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89757 q ha hb
  have h2 (q : Pattern) (ha : d270940 q = 1) (hb : d300100 q = 1) : d330918 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270940, d330918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270940, d330918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270941 q = 1) (hb : d300100 q = 1) : d330919 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270941, d330919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270941, d330919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d270942 q = 1) (hb : d300100 q = 1) : d330920 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270942, d330920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270942, d330920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270943 q = 1) (hb : d300100 q = 1) : d330921 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270943, d330921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270943, d330921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270944 q = 1) (hb : d300100 q = 1) : d330922 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270944, d330922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270944, d330922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90252 (p : Pattern) (ha : d270950 p = 1) (hb : d300100 p = 1) : d330928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37076 q = 1) (hb : d300100 q = 1) : d330193 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d37076, d330193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89747 q ha hb
    | true =>
      simp only [d37076, d330193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89750 q ha hb
  have h2 (q : Pattern) (ha : d37077 q = 1) (hb : d300100 q = 1) : d330194 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d37077, d330194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37077, d330194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d270931 q = 1) (hb : d300100 q = 1) : d330909 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270931, d330909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270931, d330909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d270932 q = 1) (hb : d300100 q = 1) : d330910 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270932, d330910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270932, d330910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270934 q = 1) (hb : d300100 q = 1) : d330912 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270934, d330912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270934, d330912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90250 q ha hb
  have h6 (q : Pattern) (ha : d270935 q = 1) (hb : d300100 q = 1) : d330913 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270935, d330913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d270935, d330913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d270936 q = 1) (hb : d300100 q = 1) : d330914 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270936, d330914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d270936, d330914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d270937 q = 1) (hb : d300100 q = 1) : d330915 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270937, d330915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d270937, d330915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d270938 q = 1) (hb : d300100 q = 1) : d330916 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270938, d330916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d270938, d330916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d270945 q = 1) (hb : d300100 q = 1) : d330923 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270945, d330923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270945, d330923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90251 q ha hb
  have h11 (q : Pattern) (ha : d270946 q = 1) (hb : d300100 q = 1) : d330924 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270946, d330924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270946, d330924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d270947 q = 1) (hb : d300100 q = 1) : d330925 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270947, d330925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d270947, d330925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d270948 q = 1) (hb : d300100 q = 1) : d330926 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270948, d330926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d270948, d330926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d270949 q = 1) (hb : d300100 q = 1) : d330927 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270949, d330927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270949, d330927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d270950 q = 1) (hb : d300100 q = 1) : d330928 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d270950, d330928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d270950, d330928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro90253 (p : Pattern) (ha : d270956 p = 1) (hb : d300100 p = 1) : d330934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270951 q = 1) (hb : d300100 q = 1) : d330929 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d270951, d330929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270951, d330929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90252 q ha hb
  have h2 (q : Pattern) (ha : d270952 q = 1) (hb : d300100 q = 1) : d330930 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d270952, d330930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270952, d330930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270953 q = 1) (hb : d300100 q = 1) : d330931 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d270953, d330931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270953, d330931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270954 q = 1) (hb : d300100 q = 1) : d330932 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d270954, d330932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270954, d330932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270955 q = 1) (hb : d300100 q = 1) : d330933 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d270955, d330933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270955, d330933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270956 q = 1) (hb : d300100 q = 1) : d330934 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d270956, d330934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270956, d330934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90254 (p : Pattern) (ha : d300100 p = 1) (hb : d324280 p = 1) : d330940 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37632 q = 1) (hb : d300100 q = 1) : d330412 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d37632, d330412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89818 q ha hb
    | true =>
      simp only [d37632, d330412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89819 q ha hb
  have h2 (q : Pattern) (ha : d37633 q = 1) (hb : d300100 q = 1) : d330413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d37633, d330413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37633, d330413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37634 q = 1) (hb : d300100 q = 1) : d330414 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d37634, d330414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d37634, d330414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d37635 q = 1) (hb : d300100 q = 1) : d330415 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d37635, d330415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37635, d330415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d37636 q = 1) (hb : d300100 q = 1) : d330416 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d37636, d330416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37636, d330416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d300100 q = 1) (hb : d324280 q = 1) : d330940 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d324280, d330940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324280, d330940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro90255 (p : Pattern) (ha : d300100 p = 1) (hb : d324287 p = 1) : d330612 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37980 q = 1) (hb : d300100 q = 1) : d330576 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d37980, d330576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89859 q ha hb
    | true =>
      simp only [d37980, d330576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89826 q ha hb
  have h2 (q : Pattern) (ha : d37981 q = 1) (hb : d300100 q = 1) : d330577 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d37981, d330577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37981, d330577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37982 q = 1) (hb : d300100 q = 1) : d330578 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d37982, d330578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37982, d330578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d37994 q = 1) (hb : d300100 q = 1) : d330580 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d37994, d330580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89826 q ha hb
    | true =>
      simp only [d37994, d330580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89861 q ha hb
  have h5 (q : Pattern) (ha : d37995 q = 1) (hb : d300100 q = 1) : d330581 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d37995, d330581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37995, d330581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d37996 q = 1) (hb : d300100 q = 1) : d330582 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d37996, d330582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d37996, d330582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d37997 q = 1) (hb : d300100 q = 1) : d330583 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d37997, d330583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d37997, d330583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38013 q = 1) (hb : d300100 q = 1) : d330597 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38013, d330597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89826 q ha hb
    | true =>
      simp only [d38013, d330597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89827 q ha hb
  have h9 (q : Pattern) (ha : d38014 q = 1) (hb : d300100 q = 1) : d330598 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38014, d330598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38014, d330598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d38015 q = 1) (hb : d300100 q = 1) : d330599 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38015, d330599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38015, d330599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d38016 q = 1) (hb : d300100 q = 1) : d330600 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d38016, d330600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d38016, d330600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d300100 q = 1) (hb : d324286 q = 1) : d330611 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d324286, d330611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d324286, d330611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d300100 q = 1) (hb : d324287 q = 1) : d330612 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d324287, d330612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d324287, d330612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro90256 (p : Pattern) (ha : d300100 p = 1) (hb : d324293 p = 1) : d330949 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d300100 q = 1) (hb : d324288 q = 1) : d330613 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d324288, d330613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90255 q ha hb
    | true =>
      simp only [d324288, d330613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d300100 q = 1) (hb : d324289 q = 1) : d330614 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d324289, d330614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324289, d330614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38019 q = 1) (hb : d300100 q = 1) : d330603 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38019, d330603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89828 q ha hb
    | true =>
      simp only [d38019, d330603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38020 q = 1) (hb : d300100 q = 1) : d330604 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38020, d330604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38020, d330604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d300100 q = 1) (hb : d324290 q = 1) : d330946 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d324290, d330946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324290, d330946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d300100 q = 1) (hb : d324291 q = 1) : d330947 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d324291, d330947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324291, d330947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d300100 q = 1) (hb : d324292 q = 1) : d330948 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d324292, d330948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d324292, d330948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d300100 q = 1) (hb : d324293 q = 1) : d330949 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d324293, d330949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324293, d330949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro90257 (p : Pattern) (ha : d300100 p = 1) (hb : d324299 p = 1) : d330955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d300100 q = 1) (hb : d324294 q = 1) : d330950 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d324294, d330950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90256 q ha hb
    | true =>
      simp only [d324294, d330950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89829 q hb ha
  have h2 (q : Pattern) (ha : d300100 q = 1) (hb : d324295 q = 1) : d330951 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d324295, d330951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324295, d330951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d300100 q = 1) (hb : d324296 q = 1) : d330952 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d324296, d330952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324296, d330952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d300100 q = 1) (hb : d324297 q = 1) : d330953 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d324297, d330953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324297, d330953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d300100 q = 1) (hb : d324298 q = 1) : d330954 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d324298, d330954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324298, d330954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d300100 q = 1) (hb : d324299 q = 1) : d330955 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d324299, d330955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324299, d330955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90258 (p : Pattern) (ha : d300100 p = 1) (hb : d324305 p = 1) : d330961 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37638 q = 1) (hb : d300100 q = 1) : d330418 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d37638, d330418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89817 q ha hb
    | true =>
      simp only [d37638, d330418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89820 q ha hb
  have h2 (q : Pattern) (ha : d37639 q = 1) (hb : d300100 q = 1) : d330419 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d37639, d330419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d37639, d330419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d300100 q = 1) (hb : d324278 q = 1) : d330938 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324278, d330938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d324278, d330938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d300100 q = 1) (hb : d324279 q = 1) : d330939 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324279, d330939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324279, d330939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d300100 q = 1) (hb : d324281 q = 1) : d330941 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d324281, d330941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324281, d330941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90254 q ha hb
  have h6 (q : Pattern) (ha : d300100 q = 1) (hb : d324282 q = 1) : d330942 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d324282, d330942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324282, d330942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d300100 q = 1) (hb : d324283 q = 1) : d330943 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324283, d330943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d324283, d330943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d300100 q = 1) (hb : d324284 q = 1) : d330944 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324284, d330944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324284, d330944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d300100 q = 1) (hb : d324285 q = 1) : d330945 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d324285, d330945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324285, d330945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d300100 q = 1) (hb : d324300 q = 1) : d330956 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d324300, d330956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324300, d330956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90257 q ha hb
  have h11 (q : Pattern) (ha : d300100 q = 1) (hb : d324301 q = 1) : d330957 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d324301, d330957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d324301, d330957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d300100 q = 1) (hb : d324302 q = 1) : d330958 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324302, d330958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d324302, d330958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d300100 q = 1) (hb : d324303 q = 1) : d330959 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324303, d330959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d324303, d330959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d300100 q = 1) (hb : d324304 q = 1) : d330960 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d324304, d330960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d324304, d330960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d300100 q = 1) (hb : d324305 q = 1) : d330961 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d324305, d330961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d324305, d330961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro90259 (p : Pattern) (ha : d300100 p = 1) (hb : d324311 p = 1) : d330967 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d300100 q = 1) (hb : d324306 q = 1) : d330962 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d324306, d330962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324306, d330962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90258 q ha hb
  have h2 (q : Pattern) (ha : d300100 q = 1) (hb : d324307 q = 1) : d330963 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d324307, d330963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324307, d330963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d300100 q = 1) (hb : d324308 q = 1) : d330964 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d324308, d330964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324308, d330964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d300100 q = 1) (hb : d324309 q = 1) : d330965 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d324309, d330965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324309, d330965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d300100 q = 1) (hb : d324310 q = 1) : d330966 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d324310, d330966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324310, d330966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d300100 q = 1) (hb : d324311 q = 1) : d330967 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d324311, d330967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324311, d330967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90260 (p : Pattern) (ha : d300100 p = 1) (hb : d324318 p = 1) : d330974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38276 q = 1) (hb : d300100 q = 1) : d330686 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d38276, d330686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89893 q ha hb
    | true =>
      simp only [d38276, d330686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89894 q ha hb
  have h2 (q : Pattern) (ha : d38277 q = 1) (hb : d300100 q = 1) : d330687 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d38277, d330687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38277, d330687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38278 q = 1) (hb : d300100 q = 1) : d330688 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d38278, d330688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38278, d330688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38279 q = 1) (hb : d300100 q = 1) : d330689 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d38279, d330689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38279, d330689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d38280 q = 1) (hb : d300100 q = 1) : d330690 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d38280, d330690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38280, d330690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d300100 q = 1) (hb : d324318 q = 1) : d330974 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d324318, d330974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324318, d330974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro90261 (p : Pattern) (ha : d300100 p = 1) (hb : d324325 p = 1) : d330825 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38572 q = 1) (hb : d300100 q = 1) : d330794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38572, d330794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89931 q ha hb
    | true =>
      simp only [d38572, d330794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89901 q ha hb
  have h2 (q : Pattern) (ha : d38573 q = 1) (hb : d300100 q = 1) : d330795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38573, d330795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38573, d330795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38574 q = 1) (hb : d300100 q = 1) : d330796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38574, d330796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38574, d330796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38586 q = 1) (hb : d300100 q = 1) : d305446 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38586, d305446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89901 q ha hb
    | true =>
      simp only [d38586, d305446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89933 q ha hb
  have h5 (q : Pattern) (ha : d38587 q = 1) (hb : d300100 q = 1) : d305447 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38587, d305447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38587, d305447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38588 q = 1) (hb : d300100 q = 1) : d305448 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38588, d305448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38588, d305448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d38589 q = 1) (hb : d300100 q = 1) : d330797 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d38589, d330797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38589, d330797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38605 q = 1) (hb : d300100 q = 1) : d330810 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d38605, d330810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89901 q ha hb
    | true =>
      simp only [d38605, d330810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89902 q ha hb
  have h9 (q : Pattern) (ha : d38606 q = 1) (hb : d300100 q = 1) : d330811 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d38606, d330811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38606, d330811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d38607 q = 1) (hb : d300100 q = 1) : d330812 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d38607, d330812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38607, d330812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d38608 q = 1) (hb : d300100 q = 1) : d330813 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d38608, d330813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d38608, d330813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d300100 q = 1) (hb : d324324 q = 1) : d330824 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d324324, d330824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d324324, d330824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d300100 q = 1) (hb : d324325 q = 1) : d330825 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d324325, d330825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d324325, d330825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro90262 (p : Pattern) (ha : d300100 p = 1) (hb : d324331 p = 1) : d330983 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d300100 q = 1) (hb : d324326 q = 1) : d330826 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d324326, d330826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90261 q ha hb
    | true =>
      simp only [d324326, d330826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d300100 q = 1) (hb : d324327 q = 1) : d330827 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d324327, d330827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324327, d330827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38611 q = 1) (hb : d300100 q = 1) : d330816 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d38611, d330816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89903 q ha hb
    | true =>
      simp only [d38611, d330816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38612 q = 1) (hb : d300100 q = 1) : d330817 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38612, d330817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38612, d330817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d300100 q = 1) (hb : d324328 q = 1) : d330980 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d324328, d330980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324328, d330980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d300100 q = 1) (hb : d324329 q = 1) : d330981 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d324329, d330981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324329, d330981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d300100 q = 1) (hb : d324330 q = 1) : d330982 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d324330, d330982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d324330, d330982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d300100 q = 1) (hb : d324331 q = 1) : d330983 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d324331, d330983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324331, d330983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro90263 (p : Pattern) (ha : d300100 p = 1) (hb : d324333 p = 1) : d330984 p = 1 := by
  have h0 (q : Pattern) (ha : d300099 q = 1) (hb : d324332 q = 1) : d324332 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d46866 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d300100 q = 1) (hb : d324333 q = 1) : d330984 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d300100, d324333, d330984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300100, d324333, d330984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro90264 (p : Pattern) (ha : d300100 p = 1) (hb : d324339 p = 1) : d330990 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5238 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77927 q ha hb
  have h2 (q : Pattern) (ha : d300100 q = 1) (hb : d324334 q = 1) : d330985 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d324334, d330985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90263 q ha hb
    | true =>
      simp only [d324334, d330985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77926 q hb ha
  have h3 (q : Pattern) (ha : d300100 q = 1) (hb : d324335 q = 1) : d330986 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d324335, d330986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d324335, d330986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d300100 q = 1) (hb : d324336 q = 1) : d330987 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d324336, d330987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324336, d330987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d2047 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77927 q ha hb
    | true =>
      simp only [d2047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10406 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77926 q ha hb
    | true =>
      simp only [d10406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d38188 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d38188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d38189 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d38189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d38189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d300100 q = 1) (hb : d324337 q = 1) : d330988 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d324337, d330988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324337, d330988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d300100 q = 1) (hb : d324338 q = 1) : d330989 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d324338, d330989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d324338, d330989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d300100 q = 1) (hb : d324339 q = 1) : d330990 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d324339, d330990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d324339, d330990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro90265 (p : Pattern) (ha : d300100 p = 1) (hb : d324345 p = 1) : d330996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38566 q = 1) (hb : d300100 q = 1) : d305402 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38566, d305402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38566, d305402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89882 q ha hb
  have h2 (q : Pattern) (ha : d38211 q = 1) (hb : d300100 q = 1) : d305245 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38211, d305245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89882 q ha hb
    | true =>
      simp only [d38211, d305245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38567 q = 1) (hb : d300100 q = 1) : d305403 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38567, d305403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38567, d305403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d38212 q = 1) (hb : d300100 q = 1) : d305246 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38212, d305246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38212, d305246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d38568 q = 1) (hb : d300100 q = 1) : d305404 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d38568, d305404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d38568, d305404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d38569 q = 1) (hb : d300100 q = 1) : d305405 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d38569, d305405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d38569, d305405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d38603 q = 1) (hb : d300100 q = 1) : d305411 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d38603, d305411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d38603, d305411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d38580 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89885 q ha hb
  have h9 (q : Pattern) (ha : d38234 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d38234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89885 q ha hb
    | true =>
      simp only [d38234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d38581 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d38581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d38581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d300100 q = 1) (hb : d324340 q = 1) : d330991 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d324340, d330991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90264 q ha hb
    | true =>
      simp only [d324340, d330991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d300100 q = 1) (hb : d324341 q = 1) : d330992 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d324341, d330992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d324341, d330992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d300100 q = 1) (hb : d324342 q = 1) : d330993 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d324342, d330993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d324342, d330993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d300100 q = 1) (hb : d324343 q = 1) : d330994 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d324343, d330994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d324343, d330994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d300100 q = 1) (hb : d324344 q = 1) : d330995 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d324344, d330995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d324344, d330995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d300100 q = 1) (hb : d324345 q = 1) : d330996 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d324345, d330996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d324345, d330996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro90266 (p : Pattern) (ha : d300100 p = 1) (hb : d324351 p = 1) : d331002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d300100 q = 1) (hb : d324346 q = 1) : d330997 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d324346, d330997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89901 q hb ha
    | true =>
      simp only [d324346, d330997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90265 q ha hb
  have h2 (q : Pattern) (ha : d300100 q = 1) (hb : d324347 q = 1) : d330998 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d324347, d330998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324347, d330998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d300100 q = 1) (hb : d324348 q = 1) : d330999 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d324348, d330999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324348, d330999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d300100 q = 1) (hb : d324349 q = 1) : d331000 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d324349, d331000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324349, d331000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d300100 q = 1) (hb : d324350 q = 1) : d331001 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d324350, d331001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324350, d331001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d300100 q = 1) (hb : d324351 q = 1) : d331002 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d324351, d331002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324351, d331002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro90267 (p : Pattern) (ha : d300100 p = 1) (hb : d324357 p = 1) : d331008 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d300100 q = 1) (hb : d324352 q = 1) : d331003 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d324352, d331003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90266 q ha hb
    | true =>
      simp only [d324352, d331003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d300100 q = 1) (hb : d324353 q = 1) : d331004 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d324353, d331004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324353, d331004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d300100 q = 1) (hb : d324354 q = 1) : d331005 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d324354, d331005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324354, d331005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d300100 q = 1) (hb : d324355 q = 1) : d331006 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d324355, d331006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324355, d331006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d300100 q = 1) (hb : d324356 q = 1) : d331007 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d324356, d331007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324356, d331007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d300100 q = 1) (hb : d324357 q = 1) : d331008 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d324357, d331008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324357, d331008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro90268 (p : Pattern) (ha : d300100 p = 1) (hb : d324363 p = 1) : d331014 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d300100 q = 1) (hb : d324358 q = 1) : d331009 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d324358, d331009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90262 q ha hb
    | true =>
      simp only [d324358, d331009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90267 q ha hb
  have h2 (q : Pattern) (ha : d300100 q = 1) (hb : d324359 q = 1) : d331010 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d324359, d331010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324359, d331010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d300100 q = 1) (hb : d324360 q = 1) : d331011 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d324360, d331011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324360, d331011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d300100 q = 1) (hb : d324361 q = 1) : d331012 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d324361, d331012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324361, d331012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d300100 q = 1) (hb : d324362 q = 1) : d331013 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d324362, d331013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324362, d331013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d300100 q = 1) (hb : d324363 q = 1) : d331014 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d324363, d331014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324363, d331014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90269 (p : Pattern) (ha : d300100 p = 1) (hb : d324369 p = 1) : d331020 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38282 q = 1) (hb : d300100 q = 1) : d330692 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d38282, d330692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89892 q ha hb
    | true =>
      simp only [d38282, d330692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89895 q ha hb
  have h2 (q : Pattern) (ha : d38283 q = 1) (hb : d300100 q = 1) : d330693 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d38283, d330693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38283, d330693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d300100 q = 1) (hb : d324316 q = 1) : d330972 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324316, d330972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d324316, d330972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d300100 q = 1) (hb : d324317 q = 1) : d330973 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324317, d330973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324317, d330973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d300100 q = 1) (hb : d324319 q = 1) : d330975 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d324319, d330975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324319, d330975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90260 q ha hb
  have h6 (q : Pattern) (ha : d300100 q = 1) (hb : d324320 q = 1) : d330976 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d324320, d330976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324320, d330976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d300100 q = 1) (hb : d324321 q = 1) : d330977 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324321, d330977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d324321, d330977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d300100 q = 1) (hb : d324322 q = 1) : d330978 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324322, d330978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d324322, d330978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d300100 q = 1) (hb : d324323 q = 1) : d330979 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d324323, d330979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324323, d330979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d300100 q = 1) (hb : d324364 q = 1) : d331015 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d324364, d331015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324364, d331015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90268 q ha hb
  have h11 (q : Pattern) (ha : d300100 q = 1) (hb : d324365 q = 1) : d331016 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d324365, d331016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d324365, d331016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d300100 q = 1) (hb : d324366 q = 1) : d331017 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d324366, d331017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d324366, d331017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d300100 q = 1) (hb : d324367 q = 1) : d331018 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d324367, d331018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d324367, d331018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d300100 q = 1) (hb : d324368 q = 1) : d331019 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d324368, d331019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d324368, d331019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d300100 q = 1) (hb : d324369 q = 1) : d331020 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d324369, d331020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d324369, d331020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro90270 (p : Pattern) (ha : d300100 p = 1) (hb : d324375 p = 1) : d331026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d300100 q = 1) (hb : d324370 q = 1) : d331021 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d324370, d331021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324370, d331021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90269 q ha hb
  have h2 (q : Pattern) (ha : d300100 q = 1) (hb : d324371 q = 1) : d331022 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d324371, d331022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324371, d331022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d300100 q = 1) (hb : d324372 q = 1) : d331023 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d324372, d331023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324372, d331023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d300100 q = 1) (hb : d324373 q = 1) : d331024 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d324373, d331024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324373, d331024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d300100 q = 1) (hb : d324374 q = 1) : d331025 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d324374, d331025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324374, d331025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d300100 q = 1) (hb : d324375 q = 1) : d331026 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d324375, d331026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324375, d331026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90271 (p : Pattern) (ha : d300100 p = 1) (hb : d324381 p = 1) : d331032 p = 1 := by
  have h0 (q : Pattern) (ha : d270902 q = 1) (hb : d300100 q = 1) : d305577 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d270902, d305577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90241 q ha hb
    | true =>
      simp only [d270902, d305577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90245 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d270929 q = 1) (hb : d300100 q = 1) : d305604 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d270929, d305604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270929, d305604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90249 q ha hb
  have h3 (q : Pattern) (ha : d270930 q = 1) (hb : d300100 q = 1) : d305605 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d270930, d305605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270930, d305605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270957 q = 1) (hb : d300100 q = 1) : d330935 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d270957, d330935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270957, d330935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90253 q ha hb
  have h5 (q : Pattern) (ha : d270958 q = 1) (hb : d300100 q = 1) : d330936 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d270958, d330936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270958, d330936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270959 q = 1) (hb : d300100 q = 1) : d330937 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d270959, d330937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d270959, d330937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d300100 q = 1) (hb : d324312 q = 1) : d330968 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d324312, d330968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d324312, d330968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90259 q ha hb
  have h8 (q : Pattern) (ha : d300100 q = 1) (hb : d324313 q = 1) : d330969 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d324313, d330969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d324313, d330969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d300100 q = 1) (hb : d324314 q = 1) : d330970 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d324314, d330970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d324314, d330970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d300100 q = 1) (hb : d324315 q = 1) : d330971 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d324315, d330971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d324315, d330971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d300100 q = 1) (hb : d324376 q = 1) : d331027 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d324376, d331027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d324376, d331027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90270 q ha hb
  have h12 (q : Pattern) (ha : d300100 q = 1) (hb : d324377 q = 1) : d331028 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d324377, d331028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d324377, d331028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d300100 q = 1) (hb : d324378 q = 1) : d331029 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d324378, d331029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d324378, d331029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d300100 q = 1) (hb : d324379 q = 1) : d331030 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d324379, d331030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d324379, d331030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d300100 q = 1) (hb : d324380 q = 1) : d331031 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d324380, d331031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d324380, d331031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d300100 q = 1) (hb : d324381 q = 1) : d331032 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d324381, d331032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d324381, d331032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro90272 (p : Pattern) (ha : d300100 p = 1) (hb : d324387 p = 1) : d331038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d300100 q = 1) (hb : d324382 q = 1) : d331033 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d324382, d331033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90271 q ha hb
    | true =>
      simp only [d324382, d331033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d300100 q = 1) (hb : d324383 q = 1) : d331034 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d324383, d331034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324383, d331034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d300100 q = 1) (hb : d324384 q = 1) : d331035 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d324384, d331035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324384, d331035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d300100 q = 1) (hb : d324385 q = 1) : d331036 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d324385, d331036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324385, d331036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d300100 q = 1) (hb : d324386 q = 1) : d331037 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d324386, d331037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324386, d331037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d300100 q = 1) (hb : d324387 q = 1) : d331038 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d324387, d331038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324387, d331038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro90273 (p : Pattern) (ha : d300100 p = 1) (hb : d324393 p = 1) : d331044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d300100 q = 1) (hb : d324388 q = 1) : d331039 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d324388, d331039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90272 q ha hb
    | true =>
      simp only [d324388, d331039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d300100 q = 1) (hb : d324389 q = 1) : d331040 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d324389, d331040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324389, d331040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d300100 q = 1) (hb : d324390 q = 1) : d331041 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d324390, d331041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324390, d331041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d300100 q = 1) (hb : d324391 q = 1) : d331042 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d324391, d331042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324391, d331042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d300100 q = 1) (hb : d324392 q = 1) : d331043 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d324392, d331043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324392, d331043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d300100 q = 1) (hb : d324393 q = 1) : d331044 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d324393, d331044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324393, d331044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro90274 (p : Pattern) (ha : d300100 p = 1) (hb : d324399 p = 1) : d331050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d300100 q = 1) (hb : d324394 q = 1) : d331045 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d324394, d331045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90273 q ha hb
    | true =>
      simp only [d324394, d331045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d300100 q = 1) (hb : d324395 q = 1) : d331046 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d324395, d331046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324395, d331046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d300100 q = 1) (hb : d324396 q = 1) : d331047 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d324396, d331047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324396, d331047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d300100 q = 1) (hb : d324397 q = 1) : d331048 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d324397, d331048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324397, d331048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d300100 q = 1) (hb : d324398 q = 1) : d331049 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d324398, d331049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324398, d331049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d300100 q = 1) (hb : d324399 q = 1) : d331050 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d324399, d331050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324399, d331050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro90275 (p : Pattern) (ha : d300100 p = 1) (hb : d324405 p = 1) : d331056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d300100 q = 1) (hb : d324400 q = 1) : d331051 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d324400, d331051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90274 q ha hb
    | true =>
      simp only [d324400, d331051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d300100 q = 1) (hb : d324401 q = 1) : d331052 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d324401, d331052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324401, d331052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d300100 q = 1) (hb : d324402 q = 1) : d331053 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d324402, d331053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324402, d331053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d300100 q = 1) (hb : d324403 q = 1) : d331054 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d324403, d331054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324403, d331054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d300100 q = 1) (hb : d324404 q = 1) : d331055 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d324404, d331055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324404, d331055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d300100 q = 1) (hb : d324405 q = 1) : d331056 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d324405, d331056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324405, d331056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro90276 (p : Pattern) (ha : d300100 p = 1) (hb : d324411 p = 1) : d331062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d300100 q = 1) (hb : d324406 q = 1) : d331057 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d324406, d331057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90275 q ha hb
    | true =>
      simp only [d324406, d331057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d300100 q = 1) (hb : d324407 q = 1) : d331058 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d324407, d331058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324407, d331058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d300100 q = 1) (hb : d324408 q = 1) : d331059 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d324408, d331059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324408, d331059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d300100 q = 1) (hb : d324409 q = 1) : d331060 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d324409, d331060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324409, d331060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d300100 q = 1) (hb : d324410 q = 1) : d331061 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d324410, d331061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324410, d331061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d300100 q = 1) (hb : d324411 q = 1) : d331062 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d324411, d331062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324411, d331062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro90277 (p : Pattern) (ha : d300100 p = 1) (hb : d324417 p = 1) : d331068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d300100 q = 1) (hb : d324412 q = 1) : d331063 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d324412, d331063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90276 q ha hb
    | true =>
      simp only [d324412, d331063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d300100 q = 1) (hb : d324413 q = 1) : d331064 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d324413, d331064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324413, d331064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d300100 q = 1) (hb : d324414 q = 1) : d331065 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d324414, d331065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324414, d331065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d300100 q = 1) (hb : d324415 q = 1) : d331066 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d324415, d331066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324415, d331066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d300100 q = 1) (hb : d324416 q = 1) : d331067 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d324416, d331067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324416, d331067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d300100 q = 1) (hb : d324417 q = 1) : d331068 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d324417, d331068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324417, d331068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro90278 (p : Pattern) (ha : d300100 p = 1) (hb : d324423 p = 1) : d331074 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d300100 q = 1) (hb : d324418 q = 1) : d331069 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d324418, d331069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90277 q ha hb
    | true =>
      simp only [d324418, d331069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d300100 q = 1) (hb : d324419 q = 1) : d331070 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d324419, d331070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324419, d331070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d300100 q = 1) (hb : d324420 q = 1) : d331071 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d324420, d331071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324420, d331071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d300100 q = 1) (hb : d324421 q = 1) : d331072 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d324421, d331072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324421, d331072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d300100 q = 1) (hb : d324422 q = 1) : d331073 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d324422, d331073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324422, d331073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d300100 q = 1) (hb : d324423 q = 1) : d331074 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d324423, d331074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324423, d331074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro90279 (p : Pattern) (ha : d284473 p = 1) (hb : d304159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d284437 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d284443 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d284468 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d284359 q = 1) (hb : d304097 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d284359, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89957 q ha hb
    | true =>
      simp only [d284359, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d284469 q = 1) (hb : d304155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d284469, d304155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d284469, d304155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d284360 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d284470 q = 1) (hb : d304156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d284470, d304156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d284470, d304156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d284471 q = 1) (hb : d304157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d284471, d304157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d284471, d304157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d284472 q = 1) (hb : d304158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d284472, d304158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d284472, d304158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d284473 q = 1) (hb : d304159 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284473, d304159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284473, d304159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro90280 (p : Pattern) (ha : d284489 p = 1) (hb : d304166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d284437 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d284443 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d284468 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d284359 q = 1) (hb : d304097 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d284359, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89957 q ha hb
    | true =>
      simp only [d284359, d304097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d284469 q = 1) (hb : d304155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d284469, d304155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d284469, d304155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d284360 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d284470 q = 1) (hb : d304156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d284470, d304156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d284470, d304156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d284471 q = 1) (hb : d304157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d284471, d304157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d284471, d304157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d284472 q = 1) (hb : d304158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d284472, d304158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284472, d304158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d284478 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d284482 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d284484 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d284366 q = 1) (hb : d304104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d284366, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89959 q ha hb
    | true =>
      simp only [d284366, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d284485 q = 1) (hb : d304162 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d284485, d304162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d284485, d304162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d284367 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d284486 q = 1) (hb : d304163 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d284486, d304163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d284486, d304163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d284487 q = 1) (hb : d304164 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d284487, d304164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d284487, d304164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d284488 q = 1) (hb : d304165 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d284488, d304165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d284488, d304165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d284489 q = 1) (hb : d304166 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284489, d304166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d284489, d304166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro90281 (p : Pattern) (ha : d284498 p = 1) (hb : d304381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d284484 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d284366 q = 1) (hb : d304104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d284366, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89959 q ha hb
    | true =>
      simp only [d284366, d304104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d284485 q = 1) (hb : d304162 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d284485, d304162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d284485, d304162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d284367 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d284486 q = 1) (hb : d304163 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d284486, d304163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d284486, d304163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d284496 q = 1) (hb : d304164 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d284496, d304164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284496, d304164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284497 q = 1) (hb : d304165 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d284497, d304165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284497, d304165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d284498 q = 1) (hb : d304381 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284498, d304381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284498, d304381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90282 (p : Pattern) (ha : d284527 p = 1) (hb : d304427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d284522 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d284400 q = 1) (hb : d304138 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d284400, d304138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89964 q ha hb
    | true =>
      simp only [d284400, d304138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d284523 q = 1) (hb : d304423 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d284523, d304423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d284523, d304423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d284401 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d284524 q = 1) (hb : d304424 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d284524, d304424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d284524, d304424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d284525 q = 1) (hb : d304425 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d284525, d304425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284525, d304425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284526 q = 1) (hb : d304426 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d284526, d304426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284526, d304426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d284527 q = 1) (hb : d304427 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284527, d304427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284527, d304427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90283 (p : Pattern) (ha : d284533 p = 1) (hb : d305545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d284431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d284490 q = 1) (hb : d304167 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d284490, d304167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90279 q ha hb
    | true =>
      simp only [d284490, d304167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90280 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d284492 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d284493 q = 1) (hb : d304168 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d284493, d304168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d284493, d304168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d284494 q = 1) (hb : d305535 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d284494, d305535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d284494, d305535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d284495 q = 1) (hb : d305536 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d284495, d305536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284495, d305536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284499 q = 1) (hb : d304382 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d284499, d304382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d284499, d304382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90281 q ha hb
  have h8 (q : Pattern) (ha : d284500 q = 1) (hb : d305537 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d284500, d305537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d284500, d305537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d284501 q = 1) (hb : d305538 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d284501, d305538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d284501, d305538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d284502 q = 1) (hb : d305539 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d284502, d305539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d284502, d305539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d284503 q = 1) (hb : d305540 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d284503, d305540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d284503, d305540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d284528 q = 1) (hb : d304428 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d284528, d304428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d284528, d304428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90282 q ha hb
  have h13 (q : Pattern) (ha : d284529 q = 1) (hb : d305541 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d284529, d305541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d284529, d305541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d284530 q = 1) (hb : d305542 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d284530, d305542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d284530, d305542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d284531 q = 1) (hb : d305543 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d284531, d305543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d284531, d305543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d284532 q = 1) (hb : d305544 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d284532, d305544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d284532, d305544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d284533 q = 1) (hb : d305545 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d284533, d305545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d284533, d305545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro90284 (p : Pattern) (ha : d284539 p = 1) (hb : d305551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d284416 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d284534 q = 1) (hb : d305546 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d284534, d305546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d284534, d305546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90283 q ha hb
  have h3 (q : Pattern) (ha : d284535 q = 1) (hb : d305547 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d284535, d305547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d284535, d305547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d284536 q = 1) (hb : d305548 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d284536, d305548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d284536, d305548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d284537 q = 1) (hb : d305549 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d284537, d305549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d284537, d305549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d284538 q = 1) (hb : d305550 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d284538, d305550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d284538, d305550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284539 q = 1) (hb : d305551 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d284539, d305551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d284539, d305551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro90285 (p : Pattern) (ha : d304284 p = 1) (hb : d328752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d284560 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d284566 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d328747 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d284468 q = 1) (hb : d304208 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d284468, d304208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89975 q ha hb
    | true =>
      simp only [d284468, d304208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89957 q ha hb
  have h5 (q : Pattern) (ha : d304280 q = 1) (hb : d328748 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304280, d328748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304280, d328748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d284609 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304281 q = 1) (hb : d328749 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304281, d328749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d304281, d328749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d304282 q = 1) (hb : d328750 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304282, d328750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304282, d328750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d304283 q = 1) (hb : d328751 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304283, d328751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304283, d328751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d304284 q = 1) (hb : d328752 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d304284, d328752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304284, d328752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro90286 (p : Pattern) (ha : d304291 p = 1) (hb : d328759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d284560 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d284566 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d328747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d284468 q = 1) (hb : d304208 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d284468, d304208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89975 q ha hb
    | true =>
      simp only [d284468, d304208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89957 q ha hb
  have h4 (q : Pattern) (ha : d304280 q = 1) (hb : d328748 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304280, d328748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304280, d328748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d284609 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d304281 q = 1) (hb : d328749 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304281, d328749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304281, d328749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d304282 q = 1) (hb : d328750 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304282, d328750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304282, d328750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d304283 q = 1) (hb : d328751 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304283, d328751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304283, d328751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d284618 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d284622 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d328754 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d284484 q = 1) (hb : d304224 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d284484, d304224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89979 q ha hb
    | true =>
      simp only [d284484, d304224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89959 q ha hb
  have h13 (q : Pattern) (ha : d304287 q = 1) (hb : d328755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304287, d328755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d304287, d328755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d284628 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d304288 q = 1) (hb : d328756 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304288, d328756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d304288, d328756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d304289 q = 1) (hb : d328757 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304289, d328757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d304289, d328757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d304290 q = 1) (hb : d328758 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304290, d328758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d304290, d328758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d304291 q = 1) (hb : d328759 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d304291, d328759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d304291, d328759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro90287 (p : Pattern) (ha : d305554 p = 1) (hb : d328766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d328754 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d284484 q = 1) (hb : d304224 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d284484, d304224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89979 q ha hb
    | true =>
      simp only [d284484, d304224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89959 q ha hb
  have h3 (q : Pattern) (ha : d304287 q = 1) (hb : d328755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304287, d328755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304287, d328755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d284628 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d304288 q = 1) (hb : d328756 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304288, d328756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304288, d328756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d304289 q = 1) (hb : d328764 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304289, d328764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304289, d328764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d304290 q = 1) (hb : d328765 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304290, d328765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304290, d328765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305554 q = 1) (hb : d328766 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d305554, d328766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305554, d328766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90288 (p : Pattern) (ha : d305564 p = 1) (hb : d328795 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d328790 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d284522 q = 1) (hb : d304262 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d284522, d304262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89985 q ha hb
    | true =>
      simp only [d284522, d304262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89964 q ha hb
  have h3 (q : Pattern) (ha : d305560 q = 1) (hb : d328791 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305560, d328791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305560, d328791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d284679 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305561 q = 1) (hb : d328792 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d305561, d328792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305561, d328792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305562 q = 1) (hb : d328793 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d305562, d328793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305562, d328793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305563 q = 1) (hb : d328794 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d305563, d328794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305563, d328794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305564 q = 1) (hb : d328795 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d305564, d328795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305564, d328795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90289 (p : Pattern) (ha : d305570 p = 1) (hb : d328801 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d284554 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304292 q = 1) (hb : d328760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d304292, d328760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90285 q ha hb
    | true =>
      simp only [d304292, d328760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90286 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d284635 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d304293 q = 1) (hb : d328761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d304293, d328761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304293, d328761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305552 q = 1) (hb : d328762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305552, d328762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305552, d328762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305553 q = 1) (hb : d328763 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305553, d328763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305553, d328763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305555 q = 1) (hb : d328767 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d305555, d328767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305555, d328767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90287 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d284644 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d305556 q = 1) (hb : d328768 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d305556, d328768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d305556, d328768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d305557 q = 1) (hb : d328769 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305557, d328769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d305557, d328769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d305558 q = 1) (hb : d328770 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305558, d328770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d305558, d328770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d305559 q = 1) (hb : d328771 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d305559, d328771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d305559, d328771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d305565 q = 1) (hb : d328796 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d305565, d328796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305565, d328796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90288 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d284690 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d305566 q = 1) (hb : d328797 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d305566, d328797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d305566, d328797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d305567 q = 1) (hb : d328798 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305567, d328798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d305567, d328798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d305568 q = 1) (hb : d328799 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305568, d328799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d305568, d328799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d305569 q = 1) (hb : d328800 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d305569, d328800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d305569, d328800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d305570 q = 1) (hb : d328801 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d305570, d328801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d305570, d328801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro90290 (p : Pattern) (ha : d305576 p = 1) (hb : d328807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d305571 q = 1) (hb : d328802 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d305571, d328802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305571, d328802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90289 q ha hb
  have h2 (q : Pattern) (ha : d305572 q = 1) (hb : d328803 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d305572, d328803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305572, d328803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d305573 q = 1) (hb : d328804 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d305573, d328804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305573, d328804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d305574 q = 1) (hb : d328805 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d305574, d328805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305574, d328805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d305575 q = 1) (hb : d328806 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d305575, d328806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305575, d328806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305576 q = 1) (hb : d328807 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d305576, d328807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305576, d328807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90291 (p : Pattern) (ha : d304463 p = 1) (hb : d328903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d328840 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d328846 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d328892 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d304458 q = 1) (hb : d328817 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304458, d328817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90027 q ha hb
    | true =>
      simp only [d304458, d328817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90019 q hb ha
  have h5 (q : Pattern) (ha : d304459 q = 1) (hb : d328893 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304459, d328893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304459, d328893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d328899 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304460 q = 1) (hb : d328900 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304460, d328900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d304460, d328900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d304461 q = 1) (hb : d328901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304461, d328901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304461, d328901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d304462 q = 1) (hb : d328902 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304462, d328902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304462, d328902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d304463 q = 1) (hb : d328903 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d304463, d328903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304463, d328903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro90292 (p : Pattern) (ha : d304473 p = 1) (hb : d328922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d328840 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d328846 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d328892 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d304458 q = 1) (hb : d328817 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304458, d328817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90027 q ha hb
    | true =>
      simp only [d304458, d328817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90019 q hb ha
  have h4 (q : Pattern) (ha : d304459 q = 1) (hb : d328893 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304459, d328893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304459, d328893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d328899 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d304460 q = 1) (hb : d328900 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304460, d328900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304460, d328900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d304461 q = 1) (hb : d328901 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304461, d328901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304461, d328901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d304462 q = 1) (hb : d328902 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304462, d328902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304462, d328902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d328908 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d328912 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d328914 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d304468 q = 1) (hb : d328826 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304468, d328826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90029 q ha hb
    | true =>
      simp only [d304468, d328826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90020 q hb ha
  have h13 (q : Pattern) (ha : d304469 q = 1) (hb : d328915 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304469, d328915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d304469, d328915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d328918 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d304470 q = 1) (hb : d328919 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304470, d328919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d304470, d328919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d304471 q = 1) (hb : d328920 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304471, d328920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d304471, d328920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d304472 q = 1) (hb : d328921 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304472, d328921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d304472, d328921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d304473 q = 1) (hb : d328922 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d304473, d328922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d304473, d328922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro90293 (p : Pattern) (ha : d305580 p = 1) (hb : d328931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d328914 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d304468 q = 1) (hb : d328826 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304468, d328826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90029 q ha hb
    | true =>
      simp only [d304468, d328826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90020 q hb ha
  have h3 (q : Pattern) (ha : d304469 q = 1) (hb : d328915 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304469, d328915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304469, d328915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d328918 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d304470 q = 1) (hb : d328919 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304470, d328919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304470, d328919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d304471 q = 1) (hb : d328929 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304471, d328929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304471, d328929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d304472 q = 1) (hb : d328930 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304472, d328930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304472, d328930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305580 q = 1) (hb : d328931 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d305580, d328931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305580, d328931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90294 (p : Pattern) (ha : d305591 p = 1) (hb : d328987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d328975 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d305586 q = 1) (hb : d328976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d305586, d328976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90055 q ha hb
    | true =>
      simp only [d305586, d328976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90024 q hb ha
  have h3 (q : Pattern) (ha : d305587 q = 1) (hb : d328977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305587, d328977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305587, d328977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d328983 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305588 q = 1) (hb : d328984 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d305588, d328984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305588, d328984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305589 q = 1) (hb : d328985 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d305589, d328985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305589, d328985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305590 q = 1) (hb : d328986 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d305590, d328986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305590, d328986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305591 q = 1) (hb : d328987 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d305591, d328987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305591, d328987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90295 (p : Pattern) (ha : d305597 p = 1) (hb : d328993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d328834 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304474 q = 1) (hb : d328923 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d304474, d328923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90291 q ha hb
    | true =>
      simp only [d304474, d328923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90292 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d328925 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d304475 q = 1) (hb : d328926 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d304475, d328926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304475, d328926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305578 q = 1) (hb : d328927 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305578, d328927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305578, d328927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305579 q = 1) (hb : d328928 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305579, d328928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305579, d328928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305581 q = 1) (hb : d328932 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d305581, d328932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305581, d328932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90293 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d284860 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d305582 q = 1) (hb : d328933 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d305582, d328933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d305582, d328933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d305583 q = 1) (hb : d328934 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305583, d328934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d305583, d328934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d305584 q = 1) (hb : d328935 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305584, d328935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d305584, d328935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d305585 q = 1) (hb : d328936 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d305585, d328936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d305585, d328936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d305592 q = 1) (hb : d328988 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d305592, d328988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305592, d328988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90294 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d284933 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d305593 q = 1) (hb : d328989 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d305593, d328989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d305593, d328989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d305594 q = 1) (hb : d328990 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305594, d328990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d305594, d328990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d305595 q = 1) (hb : d328991 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305595, d328991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d305595, d328991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d305596 q = 1) (hb : d328992 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d305596, d328992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d305596, d328992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d305597 q = 1) (hb : d328993 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d305597, d328993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d305597, d328993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro90296 (p : Pattern) (ha : d305603 p = 1) (hb : d328999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d305598 q = 1) (hb : d328994 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d305598, d328994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305598, d328994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90295 q ha hb
  have h2 (q : Pattern) (ha : d305599 q = 1) (hb : d328995 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d305599, d328995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305599, d328995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d305600 q = 1) (hb : d328996 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d305600, d328996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305600, d328996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d305601 q = 1) (hb : d328997 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d305601, d328997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305601, d328997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d305602 q = 1) (hb : d328998 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d305602, d328998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305602, d328998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305603 q = 1) (hb : d328999 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d305603, d328999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305603, d328999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90297 (p : Pattern) (ha : d329166 p = 1) (hb : d330183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d329100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d329109 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d329155 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d329074 q = 1) (hb : d330178 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d329074, d330178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90083 q ha hb
    | true =>
      simp only [d329074, d330178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90069 q hb ha
  have h5 (q : Pattern) (ha : d329156 q = 1) (hb : d330179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d329156, d330179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d329156, d330179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d329162 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d329163 q = 1) (hb : d330180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d329163, d330180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d329163, d330180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d329164 q = 1) (hb : d330181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d329164, d330181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d329164, d330181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d329165 q = 1) (hb : d330182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d329165, d330182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d329165, d330182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d329166 q = 1) (hb : d330183 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d329166, d330183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329166, d330183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro90298 (p : Pattern) (ha : d329187 p = 1) (hb : d330192 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d329100 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d329109 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d329155 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d329074 q = 1) (hb : d330178 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d329074, d330178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90083 q ha hb
    | true =>
      simp only [d329074, d330178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90069 q hb ha
  have h4 (q : Pattern) (ha : d329156 q = 1) (hb : d330179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d329156, d330179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d329156, d330179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d329162 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d329163 q = 1) (hb : d330180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d329163, d330180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d329163, d330180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d329164 q = 1) (hb : d330181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d329164, d330181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d329164, d330181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d329165 q = 1) (hb : d330182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d329165, d330182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329165, d330182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d329172 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d329177 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d329179 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d329084 q = 1) (hb : d330187 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d329084, d330187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90085 q ha hb
    | true =>
      simp only [d329084, d330187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90070 q hb ha
  have h13 (q : Pattern) (ha : d329180 q = 1) (hb : d330188 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d329180, d330188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d329180, d330188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d329183 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d329184 q = 1) (hb : d330189 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d329184, d330189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d329184, d330189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d329185 q = 1) (hb : d330190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d329185, d330190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d329185, d330190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d329186 q = 1) (hb : d330191 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d329186, d330191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d329186, d330191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d329187 q = 1) (hb : d330192 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d329187, d330192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d329187, d330192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro90299 (p : Pattern) (ha : d329207 p = 1) (hb : d330911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d329179 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d329084 q = 1) (hb : d330187 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d329084, d330187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90085 q ha hb
    | true =>
      simp only [d329084, d330187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90070 q hb ha
  have h3 (q : Pattern) (ha : d329180 q = 1) (hb : d330188 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d329180, d330188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d329180, d330188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d329183 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d329184 q = 1) (hb : d330189 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d329184, d330189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d329184, d330189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d329205 q = 1) (hb : d330190 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d329205, d330190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329205, d330190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d329206 q = 1) (hb : d330191 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d329206, d330191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329206, d330191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d329207 q = 1) (hb : d330911 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d329207, d330911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329207, d330911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90300 (p : Pattern) (ha : d329309 p = 1) (hb : d330922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d329293 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d329298 q = 1) (hb : d330917 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d329298, d330917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90114 q ha hb
    | true =>
      simp only [d329298, d330917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90076 q hb ha
  have h3 (q : Pattern) (ha : d329299 q = 1) (hb : d330918 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d329299, d330918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d329299, d330918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d329305 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d329306 q = 1) (hb : d330919 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d329306, d330919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d329306, d330919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d329307 q = 1) (hb : d330920 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d329307, d330920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329307, d330920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d329308 q = 1) (hb : d330921 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d329308, d330921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329308, d330921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d329309 q = 1) (hb : d330922 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d329309, d330922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329309, d330922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90301 (p : Pattern) (ha : d329322 p = 1) (hb : d330928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d329092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d329188 q = 1) (hb : d330193 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d329188, d330193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90297 q ha hb
    | true =>
      simp only [d329188, d330193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90298 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d329201 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d329202 q = 1) (hb : d330194 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d329202, d330194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d329202, d330194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d329203 q = 1) (hb : d330909 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d329203, d330909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d329203, d330909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d329204 q = 1) (hb : d330910 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d329204, d330910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329204, d330910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d329208 q = 1) (hb : d330912 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d329208, d330912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d329208, d330912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90299 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d329210 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d329211 q = 1) (hb : d330913 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d329211, d330913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d329211, d330913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d329212 q = 1) (hb : d330914 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d329212, d330914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d329212, d330914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d329213 q = 1) (hb : d330915 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d329213, d330915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d329213, d330915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d329214 q = 1) (hb : d330916 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d329214, d330916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d329214, d330916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d329310 q = 1) (hb : d330923 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d329310, d330923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d329310, d330923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90300 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d329317 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d329318 q = 1) (hb : d330924 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d329318, d330924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d329318, d330924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d329319 q = 1) (hb : d330925 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d329319, d330925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d329319, d330925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d329320 q = 1) (hb : d330926 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d329320, d330926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d329320, d330926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d329321 q = 1) (hb : d330927 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d329321, d330927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d329321, d330927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d329322 q = 1) (hb : d330928 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d329322, d330928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d329322, d330928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro90302 (p : Pattern) (ha : d329328 p = 1) (hb : d330934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d329323 q = 1) (hb : d330929 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d329323, d330929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329323, d330929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90301 q ha hb
  have h2 (q : Pattern) (ha : d329324 q = 1) (hb : d330930 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d329324, d330930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329324, d330930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d329325 q = 1) (hb : d330931 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d329325, d330931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329325, d330931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d329326 q = 1) (hb : d330932 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d329326, d330932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329326, d330932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d329327 q = 1) (hb : d330933 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d329327, d330933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329327, d330933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d329328 q = 1) (hb : d330934 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d329328, d330934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329328, d330934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90303 (p : Pattern) (ha : d329488 p = 1) (hb : d330407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d329433 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d329442 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d329477 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d329407 q = 1) (hb : d330402 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d329407, d330402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90131 q ha hb
    | true =>
      simp only [d329407, d330402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90132 q ha hb
  have h5 (q : Pattern) (ha : d329478 q = 1) (hb : d330403 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d329478, d330403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d329478, d330403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d329484 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d329485 q = 1) (hb : d330404 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d329485, d330404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d329485, d330404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d329486 q = 1) (hb : d330405 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d329486, d330405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d329486, d330405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d329487 q = 1) (hb : d330406 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d329487, d330406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d329487, d330406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d329488 q = 1) (hb : d330407 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d329488, d330407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329488, d330407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro90304 (p : Pattern) (ha : d329509 p = 1) (hb : d330417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d329433 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d329442 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d329477 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d329407 q = 1) (hb : d330402 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d329407, d330402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90131 q ha hb
    | true =>
      simp only [d329407, d330402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90132 q ha hb
  have h4 (q : Pattern) (ha : d329478 q = 1) (hb : d330403 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d329478, d330403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d329478, d330403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d329484 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d329485 q = 1) (hb : d330404 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d329485, d330404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d329485, d330404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d329486 q = 1) (hb : d330405 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d329486, d330405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d329486, d330405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d329487 q = 1) (hb : d330406 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d329487, d330406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329487, d330406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d329494 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d329499 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d329501 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d329417 q = 1) (hb : d330412 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d329417, d330412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90134 q ha hb
    | true =>
      simp only [d329417, d330412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90135 q ha hb
  have h13 (q : Pattern) (ha : d329502 q = 1) (hb : d330413 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d329502, d330413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d329502, d330413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d329505 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d329506 q = 1) (hb : d330414 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d329506, d330414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d329506, d330414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d329507 q = 1) (hb : d330415 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d329507, d330415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d329507, d330415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d329508 q = 1) (hb : d330416 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d329508, d330416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d329508, d330416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d329509 q = 1) (hb : d330417 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d329509, d330417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d329509, d330417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro90305 (p : Pattern) (ha : d329529 p = 1) (hb : d330940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d329501 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d329417 q = 1) (hb : d330412 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d329417, d330412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90134 q ha hb
    | true =>
      simp only [d329417, d330412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90135 q ha hb
  have h3 (q : Pattern) (ha : d329502 q = 1) (hb : d330413 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d329502, d330413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d329502, d330413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d329505 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d329506 q = 1) (hb : d330414 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d329506, d330414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d329506, d330414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d329527 q = 1) (hb : d330415 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d329527, d330415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329527, d330415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d329528 q = 1) (hb : d330416 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d329528, d330416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329528, d330416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d329529 q = 1) (hb : d330940 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d329529, d330940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329529, d330940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90306 (p : Pattern) (ha : d329614 p = 1) (hb : d330949 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d329601 q = 1) (hb : d330613 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d329601, d330613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90174 q ha hb
    | true =>
      simp only [d329601, d330613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d329602 q = 1) (hb : d330614 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d329602, d330614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329602, d330614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d329609 q = 1) (hb : d330603 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d329609, d330603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90172 q ha hb
    | true =>
      simp only [d329609, d330603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d329610 q = 1) (hb : d330604 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d329610, d330604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329610, d330604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d329611 q = 1) (hb : d330946 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d329611, d330946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d329611, d330946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d329612 q = 1) (hb : d330947 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d329612, d330947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d329612, d330947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d329613 q = 1) (hb : d330948 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d329613, d330948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d329613, d330948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d329614 q = 1) (hb : d330949 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d329614, d330949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d329614, d330949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro90307 (p : Pattern) (ha : d329631 p = 1) (hb : d330955 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d329615 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d329620 q = 1) (hb : d330950 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d329620, d330950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90306 q ha hb
    | true =>
      simp only [d329620, d330950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90177 q ha hb
  have h3 (q : Pattern) (ha : d329621 q = 1) (hb : d330951 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d329621, d330951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d329621, d330951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d329627 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d329628 q = 1) (hb : d330952 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d329628, d330952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d329628, d330952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d329629 q = 1) (hb : d330953 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d329629, d330953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329629, d330953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d329630 q = 1) (hb : d330954 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d329630, d330954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329630, d330954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d329631 q = 1) (hb : d330955 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d329631, d330955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329631, d330955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90308 (p : Pattern) (ha : d329644 p = 1) (hb : d330961 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d329425 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d329510 q = 1) (hb : d330418 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d329510, d330418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90303 q ha hb
    | true =>
      simp only [d329510, d330418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90304 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d329523 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d329524 q = 1) (hb : d330419 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d329524, d330419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d329524, d330419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d329525 q = 1) (hb : d330938 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d329525, d330938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d329525, d330938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d329526 q = 1) (hb : d330939 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d329526, d330939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329526, d330939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d329530 q = 1) (hb : d330941 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d329530, d330941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d329530, d330941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90305 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d329532 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d329533 q = 1) (hb : d330942 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d329533, d330942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d329533, d330942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d329534 q = 1) (hb : d330943 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d329534, d330943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d329534, d330943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d329535 q = 1) (hb : d330944 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d329535, d330944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d329535, d330944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d329536 q = 1) (hb : d330945 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d329536, d330945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d329536, d330945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d329632 q = 1) (hb : d330956 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d329632, d330956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d329632, d330956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90307 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d329639 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d329640 q = 1) (hb : d330957 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d329640, d330957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d329640, d330957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d329641 q = 1) (hb : d330958 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d329641, d330958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d329641, d330958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d329642 q = 1) (hb : d330959 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d329642, d330959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d329642, d330959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d329643 q = 1) (hb : d330960 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d329643, d330960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d329643, d330960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d329644 q = 1) (hb : d330961 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d329644, d330961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d329644, d330961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro90309 (p : Pattern) (ha : d329650 p = 1) (hb : d330967 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d329645 q = 1) (hb : d330962 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d329645, d330962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329645, d330962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90308 q ha hb
  have h2 (q : Pattern) (ha : d329646 q = 1) (hb : d330963 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d329646, d330963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329646, d330963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d329647 q = 1) (hb : d330964 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d329647, d330964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329647, d330964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d329648 q = 1) (hb : d330965 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d329648, d330965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329648, d330965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d329649 q = 1) (hb : d330966 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d329649, d330966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329649, d330966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d329650 q = 1) (hb : d330967 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d329650, d330967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329650, d330967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90310 (p : Pattern) (ha : d329809 p = 1) (hb : d330681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d329763 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d329772 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d329798 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d329737 q = 1) (hb : d330676 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d329737, d330676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90188 q ha hb
    | true =>
      simp only [d329737, d330676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90189 q ha hb
  have h5 (q : Pattern) (ha : d329799 q = 1) (hb : d330677 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d329799, d330677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d329799, d330677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d329805 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d329806 q = 1) (hb : d330678 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d329806, d330678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d329806, d330678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d329807 q = 1) (hb : d330679 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d329807, d330679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d329807, d330679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d329808 q = 1) (hb : d330680 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d329808, d330680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d329808, d330680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d329809 q = 1) (hb : d330681 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d329809, d330681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329809, d330681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro90311 (p : Pattern) (ha : d329831 p = 1) (hb : d330691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d329763 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d329772 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d329798 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d329737 q = 1) (hb : d330676 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d329737, d330676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90188 q ha hb
    | true =>
      simp only [d329737, d330676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90189 q ha hb
  have h4 (q : Pattern) (ha : d329799 q = 1) (hb : d330677 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d329799, d330677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d329799, d330677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d329805 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d329806 q = 1) (hb : d330678 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d329806, d330678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d329806, d330678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d329807 q = 1) (hb : d330679 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d329807, d330679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d329807, d330679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d329808 q = 1) (hb : d330680 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d329808, d330680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329808, d330680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d329815 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d329820 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d329823 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d329747 q = 1) (hb : d330686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d329747, d330686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90191 q ha hb
    | true =>
      simp only [d329747, d330686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90192 q ha hb
  have h13 (q : Pattern) (ha : d329824 q = 1) (hb : d330687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d329824, d330687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d329824, d330687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d329827 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d329828 q = 1) (hb : d330688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d329828, d330688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d329828, d330688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d329829 q = 1) (hb : d330689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d329829, d330689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d329829, d330689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d329830 q = 1) (hb : d330690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d329830, d330690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d329830, d330690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d329831 q = 1) (hb : d330691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d329831, d330691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d329831, d330691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro90312 (p : Pattern) (ha : d329856 p = 1) (hb : d330974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d329823 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d329747 q = 1) (hb : d330686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d329747, d330686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90191 q ha hb
    | true =>
      simp only [d329747, d330686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90192 q ha hb
  have h3 (q : Pattern) (ha : d329824 q = 1) (hb : d330687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d329824, d330687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d329824, d330687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d329827 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d329828 q = 1) (hb : d330688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d329828, d330688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d329828, d330688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d329854 q = 1) (hb : d330689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d329854, d330689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329854, d330689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d329855 q = 1) (hb : d330690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d329855, d330690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329855, d330690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d329856 q = 1) (hb : d330974 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d329856, d330974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329856, d330974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90313 (p : Pattern) (ha : d329946 p = 1) (hb : d330983 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d329941 q = 1) (hb : d330826 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d329941, d330826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90223 q ha hb
    | true =>
      simp only [d329941, d330826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d329942 q = 1) (hb : d330827 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d329942, d330827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329942, d330827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d329932 q = 1) (hb : d330816 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d329932, d330816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90221 q ha hb
    | true =>
      simp only [d329932, d330816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d329933 q = 1) (hb : d330817 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d329933, d330817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329933, d330817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d329943 q = 1) (hb : d330980 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d329943, d330980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d329943, d330980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d329944 q = 1) (hb : d330981 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d329944, d330981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d329944, d330981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d329945 q = 1) (hb : d330982 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d329945, d330982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d329945, d330982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d329946 q = 1) (hb : d330983 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d329946, d330983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d329946, d330983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro90314 (p : Pattern) (ha : d263914 p = 1) (hb : d330984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263914 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44880 q = 1) (hb : d263912 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d44880, d263912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44880, d263912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46864 q = 1) (hb : d263913 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d46864, d263913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46864, d263913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d46865 q = 1) (hb : d263914 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d46865, d263914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46865, d263914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d263914 q = 1) (hb : d324332 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d324332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d324332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d263914 q = 1) (hb : d330984 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d330984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d330984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro90315 (p : Pattern) (ha : d329952 p = 1) (hb : d330990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d329947 q = 1) (hb : d330985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d329947, d330985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90314 q ha hb
    | true =>
      simp only [d329947, d330985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d329948 q = 1) (hb : d330986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d329948, d330986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329948, d330986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d329949 q = 1) (hb : d330987 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d329949, d330987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d329949, d330987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d329950 q = 1) (hb : d330988 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d329950, d330988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d329950, d330988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d329951 q = 1) (hb : d330989 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d329951, d330989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d329951, d330989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d329952 q = 1) (hb : d330990 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d329952, d330990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d329952, d330990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro90316 (p : Pattern) (ha : d329958 p = 1) (hb : d330996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d305402 q = 1) (hb : d329892 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d305402, d329892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305402, d329892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90182 q ha hb
  have h2 (q : Pattern) (ha : d305245 q = 1) (hb : d329692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d305245, d329692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90182 q ha hb
    | true =>
      simp only [d305245, d329692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d305403 q = 1) (hb : d329893 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d305403, d329893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305403, d329893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d305246 q = 1) (hb : d329693 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d305246, d329693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d305246, d329693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d305404 q = 1) (hb : d329894 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d305404, d329894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305404, d329894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305405 q = 1) (hb : d329895 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d305405, d329895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d305405, d329895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d305411 q = 1) (hb : d329924 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d305411, d329924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d305411, d329924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d329953 q = 1) (hb : d330991 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d329953, d330991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90315 q ha hb
    | true =>
      simp only [d329953, d330991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d329954 q = 1) (hb : d330992 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d329954, d330992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d329954, d330992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d329955 q = 1) (hb : d330993 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d329955, d330993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329955, d330993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d329956 q = 1) (hb : d330994 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d329956, d330994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d329956, d330994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d329957 q = 1) (hb : d330995 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d329957, d330995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d329957, d330995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d329958 q = 1) (hb : d330996 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d329958, d330996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d329958, d330996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro90317 (p : Pattern) (ha : d329964 p = 1) (hb : d331002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d329959 q = 1) (hb : d330997 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d329959, d330997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90216 q hb ha
    | true =>
      simp only [d329959, d330997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90316 q ha hb
  have h2 (q : Pattern) (ha : d329960 q = 1) (hb : d330998 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d329960, d330998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329960, d330998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d329961 q = 1) (hb : d330999 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d329961, d330999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329961, d330999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d329962 q = 1) (hb : d331000 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d329962, d331000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d329962, d331000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d329963 q = 1) (hb : d331001 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d329963, d331001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d329963, d331001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d329964 q = 1) (hb : d331002 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d329964, d331002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d329964, d331002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro90318 (p : Pattern) (ha : d329970 p = 1) (hb : d331008 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d329965 q = 1) (hb : d331003 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d329965, d331003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90317 q ha hb
    | true =>
      simp only [d329965, d331003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d329966 q = 1) (hb : d331004 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d329966, d331004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329966, d331004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d329967 q = 1) (hb : d331005 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d329967, d331005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d329967, d331005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d329968 q = 1) (hb : d331006 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d329968, d331006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d329968, d331006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d329969 q = 1) (hb : d331007 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d329969, d331007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d329969, d331007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d329970 q = 1) (hb : d331008 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d329970, d331008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d329970, d331008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro90319 (p : Pattern) (ha : d329982 p = 1) (hb : d331014 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d329938 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d329971 q = 1) (hb : d331009 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d329971, d331009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90313 q ha hb
    | true =>
      simp only [d329971, d331009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90318 q ha hb
  have h3 (q : Pattern) (ha : d329972 q = 1) (hb : d331010 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d329972, d331010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d329972, d331010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d329978 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d329979 q = 1) (hb : d331011 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d329979, d331011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d329979, d331011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d329980 q = 1) (hb : d331012 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d329980, d331012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329980, d331012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d329981 q = 1) (hb : d331013 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d329981, d331013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329981, d331013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d329982 q = 1) (hb : d331014 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d329982, d331014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329982, d331014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90320 (p : Pattern) (ha : d329999 p = 1) (hb : d331020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d329755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d329832 q = 1) (hb : d330692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d329832, d330692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90310 q ha hb
    | true =>
      simp only [d329832, d330692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90311 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d329850 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d329851 q = 1) (hb : d330693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d329851, d330693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d329851, d330693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d329852 q = 1) (hb : d330972 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d329852, d330972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d329852, d330972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d329853 q = 1) (hb : d330973 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d329853, d330973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d329853, d330973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d329857 q = 1) (hb : d330975 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d329857, d330975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d329857, d330975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90312 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d329859 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d329860 q = 1) (hb : d330976 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d329860, d330976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d329860, d330976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d329861 q = 1) (hb : d330977 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d329861, d330977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d329861, d330977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d329862 q = 1) (hb : d330978 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d329862, d330978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d329862, d330978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d329863 q = 1) (hb : d330979 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d329863, d330979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d329863, d330979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d329983 q = 1) (hb : d331015 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d329983, d331015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d329983, d331015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90319 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d329994 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d329995 q = 1) (hb : d331016 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d329995, d331016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d329995, d331016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d329996 q = 1) (hb : d331017 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d329996, d331017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d329996, d331017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d329997 q = 1) (hb : d331018 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d329997, d331018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d329997, d331018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d329998 q = 1) (hb : d331019 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d329998, d331019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d329998, d331019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d329999 q = 1) (hb : d331020 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d329999, d331020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d329999, d331020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro90321 (p : Pattern) (ha : d330005 p = 1) (hb : d331026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d330000 q = 1) (hb : d331021 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d330000, d331021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d330000, d331021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90320 q ha hb
  have h2 (q : Pattern) (ha : d330001 q = 1) (hb : d331022 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d330001, d331022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d330001, d331022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d330002 q = 1) (hb : d331023 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d330002, d331023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d330002, d331023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d330003 q = 1) (hb : d331024 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d330003, d331024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d330003, d331024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d330004 q = 1) (hb : d331025 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d330004, d331025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d330004, d331025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d330005 q = 1) (hb : d331026 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d330005, d331026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d330005, d331026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90322 (p : Pattern) (ha : d330011 p = 1) (hb : d331032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d305577 q = 1) (hb : d328808 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d305577, d328808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90284 q hb ha
    | true =>
      simp only [d305577, d328808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90290 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d305604 q = 1) (hb : d329000 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d305604, d329000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305604, d329000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90296 q ha hb
  have h3 (q : Pattern) (ha : d305605 q = 1) (hb : d329001 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d305605, d329001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305605, d329001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d329329 q = 1) (hb : d330935 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d329329, d330935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d329329, d330935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90302 q ha hb
  have h5 (q : Pattern) (ha : d329330 q = 1) (hb : d330936 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d329330, d330936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d329330, d330936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d329331 q = 1) (hb : d330937 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d329331, d330937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d329331, d330937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d329651 q = 1) (hb : d330968 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d329651, d330968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d329651, d330968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90309 q ha hb
  have h8 (q : Pattern) (ha : d329652 q = 1) (hb : d330969 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d329652, d330969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d329652, d330969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d329653 q = 1) (hb : d330970 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d329653, d330970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d329653, d330970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d329654 q = 1) (hb : d330971 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d329654, d330971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d329654, d330971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d330006 q = 1) (hb : d331027 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d330006, d331027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d330006, d331027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90321 q ha hb
  have h12 (q : Pattern) (ha : d330007 q = 1) (hb : d331028 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d330007, d331028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d330007, d331028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d330008 q = 1) (hb : d331029 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d330008, d331029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d330008, d331029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d330009 q = 1) (hb : d331030 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d330009, d331030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d330009, d331030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d330010 q = 1) (hb : d331031 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d330010, d331031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d330010, d331031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d330011 q = 1) (hb : d331032 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d330011, d331032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d330011, d331032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro90323 (p : Pattern) (ha : d330017 p = 1) (hb : d331038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d330012 q = 1) (hb : d331033 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d330012, d331033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90322 q ha hb
    | true =>
      simp only [d330012, d331033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d330013 q = 1) (hb : d331034 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d330013, d331034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330013, d331034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d330014 q = 1) (hb : d331035 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d330014, d331035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d330014, d331035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d330015 q = 1) (hb : d331036 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d330015, d331036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d330015, d331036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d330016 q = 1) (hb : d331037 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d330016, d331037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d330016, d331037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d330017 q = 1) (hb : d331038 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d330017, d331038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d330017, d331038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro90324 (p : Pattern) (ha : d330023 p = 1) (hb : d331044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d330018 q = 1) (hb : d331039 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d330018, d331039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90323 q ha hb
    | true =>
      simp only [d330018, d331039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d330019 q = 1) (hb : d331040 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d330019, d331040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330019, d331040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d330020 q = 1) (hb : d331041 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d330020, d331041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d330020, d331041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d330021 q = 1) (hb : d331042 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d330021, d331042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d330021, d331042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d330022 q = 1) (hb : d331043 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d330022, d331043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d330022, d331043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d330023 q = 1) (hb : d331044 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d330023, d331044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d330023, d331044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro90325 (p : Pattern) (ha : d330029 p = 1) (hb : d331050 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d330024 q = 1) (hb : d331045 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d330024, d331045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90324 q ha hb
    | true =>
      simp only [d330024, d331045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d330025 q = 1) (hb : d331046 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d330025, d331046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330025, d331046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d330026 q = 1) (hb : d331047 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d330026, d331047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d330026, d331047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d330027 q = 1) (hb : d331048 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d330027, d331048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d330027, d331048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d330028 q = 1) (hb : d331049 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d330028, d331049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d330028, d331049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d330029 q = 1) (hb : d331050 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d330029, d331050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d330029, d331050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro90326 (p : Pattern) (ha : d330035 p = 1) (hb : d331056 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d330030 q = 1) (hb : d331051 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d330030, d331051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90325 q ha hb
    | true =>
      simp only [d330030, d331051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d330031 q = 1) (hb : d331052 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d330031, d331052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330031, d331052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d330032 q = 1) (hb : d331053 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d330032, d331053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d330032, d331053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d330033 q = 1) (hb : d331054 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d330033, d331054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d330033, d331054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d330034 q = 1) (hb : d331055 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d330034, d331055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d330034, d331055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d330035 q = 1) (hb : d331056 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d330035, d331056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d330035, d331056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro90327 (p : Pattern) (ha : d330041 p = 1) (hb : d331062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d330036 q = 1) (hb : d331057 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d330036, d331057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90326 q ha hb
    | true =>
      simp only [d330036, d331057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d330037 q = 1) (hb : d331058 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d330037, d331058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330037, d331058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d330038 q = 1) (hb : d331059 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d330038, d331059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d330038, d331059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d330039 q = 1) (hb : d331060 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d330039, d331060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d330039, d331060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d330040 q = 1) (hb : d331061 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d330040, d331061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d330040, d331061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d330041 q = 1) (hb : d331062 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d330041, d331062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d330041, d331062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro90328 (p : Pattern) (ha : d330047 p = 1) (hb : d331068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d330042 q = 1) (hb : d331063 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d330042, d331063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90327 q ha hb
    | true =>
      simp only [d330042, d331063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d330043 q = 1) (hb : d331064 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d330043, d331064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330043, d331064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d330044 q = 1) (hb : d331065 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d330044, d331065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d330044, d331065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d330045 q = 1) (hb : d331066 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d330045, d331066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d330045, d331066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d330046 q = 1) (hb : d331067 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d330046, d331067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d330046, d331067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d330047 q = 1) (hb : d331068 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d330047, d331068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d330047, d331068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro90329 (p : Pattern) (ha : d330053 p = 1) (hb : d331074 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d330048 q = 1) (hb : d331069 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d330048, d331069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90328 q ha hb
    | true =>
      simp only [d330048, d331069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d330049 q = 1) (hb : d331070 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d330049, d331070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330049, d331070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d330050 q = 1) (hb : d331071 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d330050, d331071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d330050, d331071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d330051 q = 1) (hb : d331072 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d330051, d331072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d330051, d331072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d330052 q = 1) (hb : d331073 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d330052, d331073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d330052, d331073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d330053 q = 1) (hb : d331074 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d330053, d331074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d330053, d331074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro90330 (p : Pattern) (ha : d287442 p = 1) (hb : d304159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d282387 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282393 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d282418 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d304097 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d287438 q = 1) (hb : d304155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287438, d304155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d287438, d304155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d282310 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d287439 q = 1) (hb : d304156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d287439, d304156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d287439, d304156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d287440 q = 1) (hb : d304157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d287440, d304157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d287440, d304157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287441 q = 1) (hb : d304158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d287441, d304158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d287441, d304158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d287442 q = 1) (hb : d304159 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d287442, d304159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287442, d304159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro90331 (p : Pattern) (ha : d287447 p = 1) (hb : d304166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282387 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d282393 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282418 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d304097 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d287438 q = 1) (hb : d304155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287438, d304155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d287438, d304155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d282310 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d287439 q = 1) (hb : d304156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d287439, d304156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d287439, d304156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d287440 q = 1) (hb : d304157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d287440, d304157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d287440, d304157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d287441 q = 1) (hb : d304158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d287441, d304158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d287441, d304158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d282453 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d282457 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d282459 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d304104 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d287443 q = 1) (hb : d304162 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287443, d304162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d287443, d304162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d282317 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d287444 q = 1) (hb : d304163 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d287444, d304163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d287444, d304163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d287445 q = 1) (hb : d304164 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d287445, d304164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d287445, d304164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d287446 q = 1) (hb : d304165 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d287446, d304165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d287446, d304165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d287447 q = 1) (hb : d304166 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d287447, d304166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d287447, d304166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro90332 (p : Pattern) (ha : d287454 p = 1) (hb : d304381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d282459 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d304104 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d287443 q = 1) (hb : d304162 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287443, d304162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d287443, d304162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d282317 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d287444 q = 1) (hb : d304163 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d287444, d304163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287444, d304163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d287452 q = 1) (hb : d304164 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d287452, d304164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287452, d304164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287453 q = 1) (hb : d304165 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d287453, d304165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287453, d304165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d287454 q = 1) (hb : d304381 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d287454, d304381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287454, d304381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90333 (p : Pattern) (ha : d287464 p = 1) (hb : d304427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d282499 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d304138 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d287460 q = 1) (hb : d304423 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287460, d304423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d287460, d304423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d282351 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d287461 q = 1) (hb : d304424 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d287461, d304424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287461, d304424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d287462 q = 1) (hb : d304425 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d287462, d304425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287462, d304425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287463 q = 1) (hb : d304426 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d287463, d304426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287463, d304426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d287464 q = 1) (hb : d304427 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d287464, d304427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287464, d304427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90334 (p : Pattern) (ha : d287470 p = 1) (hb : d305545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d287448 q = 1) (hb : d304167 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d287448, d304167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90330 q ha hb
    | true =>
      simp only [d287448, d304167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90331 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282469 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d287449 q = 1) (hb : d304168 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d287449, d304168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287449, d304168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d287450 q = 1) (hb : d305535 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d287450, d305535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d287450, d305535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287451 q = 1) (hb : d305536 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d287451, d305536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d287451, d305536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287455 q = 1) (hb : d304382 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d287455, d304382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d287455, d304382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90332 q ha hb
  have h8 (q : Pattern) (ha : d287456 q = 1) (hb : d305537 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d287456, d305537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d287456, d305537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d287457 q = 1) (hb : d305538 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d287457, d305538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d287457, d305538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d287458 q = 1) (hb : d305539 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d287458, d305539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d287458, d305539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d287459 q = 1) (hb : d305540 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d287459, d305540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d287459, d305540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d287465 q = 1) (hb : d304428 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d287465, d304428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d287465, d304428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90333 q ha hb
  have h13 (q : Pattern) (ha : d287466 q = 1) (hb : d305541 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d287466, d305541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d287466, d305541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d287467 q = 1) (hb : d305542 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d287467, d305542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d287467, d305542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d287468 q = 1) (hb : d305543 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d287468, d305543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d287468, d305543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d287469 q = 1) (hb : d305544 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d287469, d305544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d287469, d305544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d287470 q = 1) (hb : d305545 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d287470, d305545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d287470, d305545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro90335 (p : Pattern) (ha : d287476 p = 1) (hb : d305551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282366 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d287471 q = 1) (hb : d305546 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d287471, d305546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287471, d305546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90334 q ha hb
  have h3 (q : Pattern) (ha : d287472 q = 1) (hb : d305547 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d287472, d305547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287472, d305547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d287473 q = 1) (hb : d305548 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d287473, d305548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287473, d305548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d287474 q = 1) (hb : d305549 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d287474, d305549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287474, d305549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d287475 q = 1) (hb : d305550 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d287475, d305550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287475, d305550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d287476 q = 1) (hb : d305551 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d287476, d305551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d287476, d305551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro90336 (p : Pattern) (ha : d304284 p = 1) (hb : d331079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d282556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282562 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d326970 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d304208 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d304280 q = 1) (hb : d331075 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304280, d331075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304280, d331075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d282630 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304281 q = 1) (hb : d331076 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304281, d331076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d304281, d331076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d304282 q = 1) (hb : d331077 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304282, d331077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304282, d331077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d304283 q = 1) (hb : d331078 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304283, d331078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304283, d331078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d304284 q = 1) (hb : d331079 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d304284, d331079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304284, d331079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro90337 (p : Pattern) (ha : d304291 p = 1) (hb : d331084 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282556 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d282562 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d326970 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d304208 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d304280 q = 1) (hb : d331075 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304280, d331075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304280, d331075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d282630 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d304281 q = 1) (hb : d331076 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304281, d331076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304281, d331076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d304282 q = 1) (hb : d331077 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304282, d331077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304282, d331077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d304283 q = 1) (hb : d331078 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304283, d331078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304283, d331078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d282639 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d282643 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d326977 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d304224 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d304287 q = 1) (hb : d331080 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304287, d331080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d304287, d331080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d282651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d304288 q = 1) (hb : d331081 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304288, d331081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d304288, d331081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d304289 q = 1) (hb : d331082 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304289, d331082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d304289, d331082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d304290 q = 1) (hb : d331083 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304290, d331083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d304290, d331083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d304291 q = 1) (hb : d331084 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d304291, d331084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d304291, d331084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro90338 (p : Pattern) (ha : d305554 p = 1) (hb : d331091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d326977 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d304224 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d304287 q = 1) (hb : d331080 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304287, d331080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304287, d331080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d282651 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d304288 q = 1) (hb : d331081 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304288, d331081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304288, d331081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d304289 q = 1) (hb : d331089 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304289, d331089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304289, d331089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d304290 q = 1) (hb : d331090 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304290, d331090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304290, d331090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305554 q = 1) (hb : d331091 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d305554, d331091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305554, d331091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90339 (p : Pattern) (ha : d305564 p = 1) (hb : d331101 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d327013 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d304262 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d305560 q = 1) (hb : d331097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305560, d331097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305560, d331097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d282721 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305561 q = 1) (hb : d331098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d305561, d331098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305561, d331098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305562 q = 1) (hb : d331099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d305562, d331099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305562, d331099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305563 q = 1) (hb : d331100 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d305563, d331100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305563, d331100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305564 q = 1) (hb : d331101 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d305564, d331101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305564, d331101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90340 (p : Pattern) (ha : d305570 p = 1) (hb : d331107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d282550 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304292 q = 1) (hb : d331085 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d304292, d331085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90336 q ha hb
    | true =>
      simp only [d304292, d331085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90337 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282658 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d304293 q = 1) (hb : d331086 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d304293, d331086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304293, d331086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305552 q = 1) (hb : d331087 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305552, d331087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305552, d331087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305553 q = 1) (hb : d331088 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305553, d331088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305553, d331088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305555 q = 1) (hb : d331092 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d305555, d331092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305555, d331092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90338 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d282667 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d305556 q = 1) (hb : d331093 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d305556, d331093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d305556, d331093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d305557 q = 1) (hb : d331094 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305557, d331094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d305557, d331094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d305558 q = 1) (hb : d331095 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305558, d331095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d305558, d331095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d305559 q = 1) (hb : d331096 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d305559, d331096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d305559, d331096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d305565 q = 1) (hb : d331102 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d305565, d331102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305565, d331102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90339 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d282732 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d305566 q = 1) (hb : d331103 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d305566, d331103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d305566, d331103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d305567 q = 1) (hb : d331104 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305567, d331104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d305567, d331104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d305568 q = 1) (hb : d331105 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305568, d331105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d305568, d331105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d305569 q = 1) (hb : d331106 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d305569, d331106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d305569, d331106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d305570 q = 1) (hb : d331107 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d305570, d331107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d305570, d331107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro90341 (p : Pattern) (ha : d305576 p = 1) (hb : d331113 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d305571 q = 1) (hb : d331108 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d305571, d331108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305571, d331108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90340 q ha hb
  have h2 (q : Pattern) (ha : d305572 q = 1) (hb : d331109 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d305572, d331109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305572, d331109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d305573 q = 1) (hb : d331110 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d305573, d331110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305573, d331110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d305574 q = 1) (hb : d331111 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d305574, d331111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305574, d331111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d305575 q = 1) (hb : d331112 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d305575, d331112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305575, d331112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305576 q = 1) (hb : d331113 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d305576, d331113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305576, d331113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90342 (p : Pattern) (ha : d304463 p = 1) (hb : d331119 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d327063 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d327069 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d327115 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d304458 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d304459 q = 1) (hb : d331115 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304459, d331115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304459, d331115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d327145 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304460 q = 1) (hb : d331116 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304460, d331116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d304460, d331116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d304461 q = 1) (hb : d331117 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304461, d331117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304461, d331117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d304462 q = 1) (hb : d331118 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304462, d331118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304462, d331118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d304463 q = 1) (hb : d331119 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d304463, d331119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304463, d331119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro90343 (p : Pattern) (ha : d304473 p = 1) (hb : d331124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d327063 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d327069 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d327115 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d304458 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d304459 q = 1) (hb : d331115 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304459, d331115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d304459, d331115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d327145 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d304460 q = 1) (hb : d331116 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304460, d331116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d304460, d331116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d304461 q = 1) (hb : d331117 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304461, d331117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304461, d331117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d304462 q = 1) (hb : d331118 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304462, d331118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304462, d331118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d327154 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d327158 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d327160 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d304468 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d304469 q = 1) (hb : d331120 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304469, d331120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d304469, d331120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d327166 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d304470 q = 1) (hb : d331121 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304470, d331121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d304470, d331121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d304471 q = 1) (hb : d331122 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304471, d331122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d304471, d331122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d304472 q = 1) (hb : d331123 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304472, d331123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d304472, d331123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d304473 q = 1) (hb : d331124 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d304473, d331124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d304473, d331124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro90344 (p : Pattern) (ha : d305580 p = 1) (hb : d331131 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d327160 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d304468 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d304469 q = 1) (hb : d331120 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d304469, d331120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304469, d331120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d327166 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d304470 q = 1) (hb : d331121 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d304470, d331121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d304470, d331121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d304471 q = 1) (hb : d331129 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d304471, d331129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304471, d331129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d304472 q = 1) (hb : d331130 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d304472, d331130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d304472, d331130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305580 q = 1) (hb : d331131 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d305580, d331131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305580, d331131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90345 (p : Pattern) (ha : d305591 p = 1) (hb : d331141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d327223 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d305586 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d305587 q = 1) (hb : d331137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305587, d331137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305587, d331137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d327249 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305588 q = 1) (hb : d331138 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d305588, d331138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305588, d331138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305589 q = 1) (hb : d331139 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d305589, d331139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305589, d331139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305590 q = 1) (hb : d331140 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d305590, d331140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305590, d331140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305591 q = 1) (hb : d331141 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d305591, d331141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305591, d331141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90346 (p : Pattern) (ha : d305597 p = 1) (hb : d331147 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d327057 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d304474 q = 1) (hb : d331125 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d304474, d331125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90342 q ha hb
    | true =>
      simp only [d304474, d331125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90343 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d327173 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d304475 q = 1) (hb : d331126 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d304475, d331126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d304475, d331126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d305578 q = 1) (hb : d331127 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305578, d331127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d305578, d331127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305579 q = 1) (hb : d331128 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305579, d331128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305579, d331128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d305581 q = 1) (hb : d331132 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d305581, d331132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305581, d331132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90344 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d282950 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d305582 q = 1) (hb : d331133 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d305582, d331133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d305582, d331133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d305583 q = 1) (hb : d331134 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305583, d331134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d305583, d331134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d305584 q = 1) (hb : d331135 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305584, d331135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d305584, d331135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d305585 q = 1) (hb : d331136 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d305585, d331136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d305585, d331136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d305592 q = 1) (hb : d331142 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d305592, d331142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d305592, d331142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90345 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d283055 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d305593 q = 1) (hb : d331143 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d305593, d331143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d305593, d331143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d305594 q = 1) (hb : d331144 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d305594, d331144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d305594, d331144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d305595 q = 1) (hb : d331145 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d305595, d331145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d305595, d331145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d305596 q = 1) (hb : d331146 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d305596, d331146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d305596, d331146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d305597 q = 1) (hb : d331147 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d305597, d331147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d305597, d331147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro90347 (p : Pattern) (ha : d305603 p = 1) (hb : d331153 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d305598 q = 1) (hb : d331148 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d305598, d331148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305598, d331148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90346 q ha hb
  have h2 (q : Pattern) (ha : d305599 q = 1) (hb : d331149 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d305599, d331149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305599, d331149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d305600 q = 1) (hb : d331150 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d305600, d331150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305600, d331150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d305601 q = 1) (hb : d331151 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d305601, d331151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305601, d331151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d305602 q = 1) (hb : d331152 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d305602, d331152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305602, d331152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d305603 q = 1) (hb : d331153 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d305603, d331153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305603, d331153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90348 (p : Pattern) (ha : d330183 p = 1) (hb : d331160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d327366 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d327375 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d327421 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d330178 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d330179 q = 1) (hb : d331156 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d330179, d331156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d330179, d331156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d327507 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d330180 q = 1) (hb : d331157 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d330180, d331157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d330180, d331157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d330181 q = 1) (hb : d331158 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d330181, d331158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d330181, d331158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d330182 q = 1) (hb : d331159 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d330182, d331159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330182, d331159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d330183 q = 1) (hb : d331160 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d330183, d331160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330183, d331160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro90349 (p : Pattern) (ha : d330192 p = 1) (hb : d331165 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d327366 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d327375 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d327421 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d330178 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d330179 q = 1) (hb : d331156 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d330179, d331156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d330179, d331156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d327507 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d330180 q = 1) (hb : d331157 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d330180, d331157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d330180, d331157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d330181 q = 1) (hb : d331158 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d330181, d331158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330181, d331158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d330182 q = 1) (hb : d331159 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d330182, d331159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330182, d331159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d327517 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d327522 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d327524 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d330187 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d330188 q = 1) (hb : d331161 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d330188, d331161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d330188, d331161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d327531 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d330189 q = 1) (hb : d331162 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d330189, d331162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d330189, d331162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d330190 q = 1) (hb : d331163 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d330190, d331163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d330190, d331163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d330191 q = 1) (hb : d331164 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d330191, d331164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d330191, d331164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d330192 q = 1) (hb : d331165 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d330192, d331165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d330192, d331165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro90350 (p : Pattern) (ha : d330911 p = 1) (hb : d331172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d327524 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d330187 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d330188 q = 1) (hb : d331161 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d330188, d331161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330188, d331161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d327531 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d330189 q = 1) (hb : d331162 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d330189, d331162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d330189, d331162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d330190 q = 1) (hb : d331170 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d330190, d331170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330190, d331170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d330191 q = 1) (hb : d331171 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d330191, d331171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330191, d331171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d330911 q = 1) (hb : d331172 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d330911, d331172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330911, d331172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90351 (p : Pattern) (ha : d330922 p = 1) (hb : d331182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d327641 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d330917 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d330918 q = 1) (hb : d331178 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d330918, d331178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330918, d331178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d327700 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d330919 q = 1) (hb : d331179 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d330919, d331179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d330919, d331179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d330920 q = 1) (hb : d331180 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d330920, d331180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330920, d331180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d330921 q = 1) (hb : d331181 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d330921, d331181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330921, d331181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d330922 q = 1) (hb : d331182 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d330922, d331182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330922, d331182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90352 (p : Pattern) (ha : d330928 p = 1) (hb : d331188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d327358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d330193 q = 1) (hb : d331166 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d330193, d331166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90348 q ha hb
    | true =>
      simp only [d330193, d331166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90349 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d327549 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d330194 q = 1) (hb : d331167 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d330194, d331167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330194, d331167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d330909 q = 1) (hb : d331168 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d330909, d331168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d330909, d331168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d330910 q = 1) (hb : d331169 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d330910, d331169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330910, d331169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d330912 q = 1) (hb : d331173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d330912, d331173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d330912, d331173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90350 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d327558 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d330913 q = 1) (hb : d331174 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d330913, d331174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d330913, d331174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d330914 q = 1) (hb : d331175 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d330914, d331175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d330914, d331175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d330915 q = 1) (hb : d331176 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d330915, d331176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d330915, d331176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d330916 q = 1) (hb : d331177 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d330916, d331177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d330916, d331177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d330923 q = 1) (hb : d331183 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d330923, d331183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d330923, d331183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90351 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d327716 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d330924 q = 1) (hb : d331184 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d330924, d331184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d330924, d331184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d330925 q = 1) (hb : d331185 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d330925, d331185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d330925, d331185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d330926 q = 1) (hb : d331186 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d330926, d331186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d330926, d331186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d330927 q = 1) (hb : d331187 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d330927, d331187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d330927, d331187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d330928 q = 1) (hb : d331188 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d330928, d331188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d330928, d331188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro90353 (p : Pattern) (ha : d330934 p = 1) (hb : d331194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d330929 q = 1) (hb : d331189 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d330929, d331189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330929, d331189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90352 q ha hb
  have h2 (q : Pattern) (ha : d330930 q = 1) (hb : d331190 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d330930, d331190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330930, d331190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d330931 q = 1) (hb : d331191 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d330931, d331191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330931, d331191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d330932 q = 1) (hb : d331192 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d330932, d331192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330932, d331192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d330933 q = 1) (hb : d331193 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d330933, d331193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330933, d331193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d330934 q = 1) (hb : d331194 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d330934, d331194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330934, d331194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90354 (p : Pattern) (ha : d330407 p = 1) (hb : d331202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d327832 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d327841 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d327876 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d330402 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d330403 q = 1) (hb : d331198 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d330403, d331198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d330403, d331198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d327962 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d330404 q = 1) (hb : d331199 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d330404, d331199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d330404, d331199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d330405 q = 1) (hb : d331200 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d330405, d331200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d330405, d331200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d330406 q = 1) (hb : d331201 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d330406, d331201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330406, d331201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d330407 q = 1) (hb : d331202 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d330407, d331202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330407, d331202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro90355 (p : Pattern) (ha : d330417 p = 1) (hb : d331207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d327832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d327841 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d327876 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d330402 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d330403 q = 1) (hb : d331198 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d330403, d331198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d330403, d331198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d327962 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d330404 q = 1) (hb : d331199 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d330404, d331199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d330404, d331199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d330405 q = 1) (hb : d331200 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d330405, d331200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330405, d331200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d330406 q = 1) (hb : d331201 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d330406, d331201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330406, d331201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d327972 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d327977 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d327979 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d330412 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d330413 q = 1) (hb : d331203 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d330413, d331203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d330413, d331203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d327986 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d330414 q = 1) (hb : d331204 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d330414, d331204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d330414, d331204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d330415 q = 1) (hb : d331205 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d330415, d331205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d330415, d331205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d330416 q = 1) (hb : d331206 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d330416, d331206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d330416, d331206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d330417 q = 1) (hb : d331207 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d330417, d331207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d330417, d331207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro90356 (p : Pattern) (ha : d330940 p = 1) (hb : d331214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d327979 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d330412 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d330413 q = 1) (hb : d331203 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d330413, d331203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330413, d331203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d327986 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d330414 q = 1) (hb : d331204 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d330414, d331204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d330414, d331204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d330415 q = 1) (hb : d331212 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d330415, d331212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330415, d331212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d330416 q = 1) (hb : d331213 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d330416, d331213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330416, d331213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d330940 q = 1) (hb : d331214 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d330940, d331214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330940, d331214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90357 (p : Pattern) (ha : d330955 p = 1) (hb : d331224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d328096 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d330950 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d330951 q = 1) (hb : d331220 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d330951, d331220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330951, d331220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d328155 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d330952 q = 1) (hb : d331221 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d330952, d331221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d330952, d331221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d330953 q = 1) (hb : d331222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d330953, d331222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330953, d331222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d330954 q = 1) (hb : d331223 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d330954, d331223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330954, d331223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d330955 q = 1) (hb : d331224 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d330955, d331224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330955, d331224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90358 (p : Pattern) (ha : d330961 p = 1) (hb : d331230 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d327824 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d330418 q = 1) (hb : d331208 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d330418, d331208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90354 q ha hb
    | true =>
      simp only [d330418, d331208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90355 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d328004 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d330419 q = 1) (hb : d331209 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d330419, d331209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330419, d331209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d330938 q = 1) (hb : d331210 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d330938, d331210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d330938, d331210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d330939 q = 1) (hb : d331211 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d330939, d331211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330939, d331211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d330941 q = 1) (hb : d331215 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d330941, d331215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d330941, d331215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90356 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d328013 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d330942 q = 1) (hb : d331216 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d330942, d331216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d330942, d331216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d330943 q = 1) (hb : d331217 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d330943, d331217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d330943, d331217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d330944 q = 1) (hb : d331218 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d330944, d331218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d330944, d331218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d330945 q = 1) (hb : d331219 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d330945, d331219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d330945, d331219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d330956 q = 1) (hb : d331225 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d330956, d331225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d330956, d331225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90357 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d328171 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d330957 q = 1) (hb : d331226 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d330957, d331226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d330957, d331226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d330958 q = 1) (hb : d331227 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d330958, d331227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d330958, d331227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d330959 q = 1) (hb : d331228 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d330959, d331228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d330959, d331228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d330960 q = 1) (hb : d331229 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d330960, d331229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d330960, d331229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d330961 q = 1) (hb : d331230 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d330961, d331230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d330961, d331230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro90359 (p : Pattern) (ha : d330967 p = 1) (hb : d331236 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d330962 q = 1) (hb : d331231 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d330962, d331231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330962, d331231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90358 q ha hb
  have h2 (q : Pattern) (ha : d330963 q = 1) (hb : d331232 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d330963, d331232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330963, d331232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d330964 q = 1) (hb : d331233 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d330964, d331233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330964, d331233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d330965 q = 1) (hb : d331234 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d330965, d331234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330965, d331234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d330966 q = 1) (hb : d331235 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d330966, d331235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330966, d331235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d330967 q = 1) (hb : d331236 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d330967, d331236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330967, d331236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90360 (p : Pattern) (ha : d330681 p = 1) (hb : d331245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d328295 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d328304 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d328330 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d330676 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d330677 q = 1) (hb : d331241 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d330677, d331241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d330677, d331241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d328420 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d330678 q = 1) (hb : d331242 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d330678, d331242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d330678, d331242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d330679 q = 1) (hb : d331243 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d330679, d331243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d330679, d331243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d330680 q = 1) (hb : d331244 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d330680, d331244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330680, d331244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d330681 q = 1) (hb : d331245 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d330681, d331245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330681, d331245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro90361 (p : Pattern) (ha : d330691 p = 1) (hb : d331250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d328295 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d328304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d328330 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d330676 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d330677 q = 1) (hb : d331241 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d330677, d331241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d330677, d331241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d328420 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d330678 q = 1) (hb : d331242 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d330678, d331242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d330678, d331242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d330679 q = 1) (hb : d331243 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d330679, d331243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330679, d331243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d330680 q = 1) (hb : d331244 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d330680, d331244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330680, d331244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d328430 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d328435 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d328438 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d330686 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d330687 q = 1) (hb : d331246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d330687, d331246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d330687, d331246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d328445 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d330688 q = 1) (hb : d331247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d330688, d331247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d330688, d331247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d330689 q = 1) (hb : d331248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d330689, d331248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d330689, d331248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d330690 q = 1) (hb : d331249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d330690, d331249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d330690, d331249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d330691 q = 1) (hb : d331250 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d330691, d331250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d330691, d331250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro90362 (p : Pattern) (ha : d330974 p = 1) (hb : d331257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d328438 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d330686 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d330687 q = 1) (hb : d331246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d330687, d331246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330687, d331246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d328445 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d330688 q = 1) (hb : d331247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d330688, d331247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d330688, d331247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d330689 q = 1) (hb : d331255 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d330689, d331255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330689, d331255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d330690 q = 1) (hb : d331256 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d330690, d331256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330690, d331256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d330974 q = 1) (hb : d331257 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d330974, d331257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330974, d331257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90363 (p : Pattern) (ha : d331014 p = 1) (hb : d331267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d328556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d331009 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d331010 q = 1) (hb : d331263 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d331010, d331263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d331010, d331263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d328649 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d331011 q = 1) (hb : d331264 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d331011, d331264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d331011, d331264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d331012 q = 1) (hb : d331265 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d331012, d331265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d331012, d331265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d331013 q = 1) (hb : d331266 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d331013, d331266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d331013, d331266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d331014 q = 1) (hb : d331267 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d331014, d331267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d331014, d331267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90364 (p : Pattern) (ha : d331020 p = 1) (hb : d331273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d328287 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d330692 q = 1) (hb : d331251 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d330692, d331251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90360 q ha hb
    | true =>
      simp only [d330692, d331251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90361 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d328468 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d330693 q = 1) (hb : d331252 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d330693, d331252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330693, d331252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d330972 q = 1) (hb : d331253 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d330972, d331253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d330972, d331253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d330973 q = 1) (hb : d331254 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d330973, d331254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d330973, d331254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d330975 q = 1) (hb : d331258 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d330975, d331258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d330975, d331258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90362 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d328477 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d330976 q = 1) (hb : d331259 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d330976, d331259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d330976, d331259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d330977 q = 1) (hb : d331260 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d330977, d331260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d330977, d331260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d330978 q = 1) (hb : d331261 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d330978, d331261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d330978, d331261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d330979 q = 1) (hb : d331262 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d330979, d331262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d330979, d331262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d331015 q = 1) (hb : d331268 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d331015, d331268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d331015, d331268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90363 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d328665 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d331016 q = 1) (hb : d331269 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d331016, d331269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d331016, d331269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d331017 q = 1) (hb : d331270 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d331017, d331270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d331017, d331270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d331018 q = 1) (hb : d331271 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d331018, d331271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d331018, d331271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d331019 q = 1) (hb : d331272 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d331019, d331272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d331019, d331272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d331020 q = 1) (hb : d331273 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d331020, d331273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d331020, d331273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro90365 (p : Pattern) (ha : d331026 p = 1) (hb : d331279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331021 q = 1) (hb : d331274 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d331021, d331274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d331021, d331274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90364 q ha hb
  have h2 (q : Pattern) (ha : d331022 q = 1) (hb : d331275 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d331022, d331275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d331022, d331275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d331023 q = 1) (hb : d331276 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d331023, d331276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d331023, d331276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d331024 q = 1) (hb : d331277 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d331024, d331277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d331024, d331277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d331025 q = 1) (hb : d331278 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d331025, d331278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d331025, d331278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d331026 q = 1) (hb : d331279 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d331026, d331279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d331026, d331279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90366 (p : Pattern) (ha : d331032 p = 1) (hb : d331285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d305577 q = 1) (hb : d331114 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d305577, d331114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90335 q hb ha
    | true =>
      simp only [d305577, d331114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90341 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d305604 q = 1) (hb : d331154 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d305604, d331154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305604, d331154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90347 q ha hb
  have h3 (q : Pattern) (ha : d305605 q = 1) (hb : d331155 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d305605, d331155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305605, d331155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d330935 q = 1) (hb : d331195 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d330935, d331195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330935, d331195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90353 q ha hb
  have h5 (q : Pattern) (ha : d330936 q = 1) (hb : d331196 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d330936, d331196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330936, d331196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d330937 q = 1) (hb : d331197 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d330937, d331197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d330937, d331197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d330968 q = 1) (hb : d331237 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d330968, d331237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330968, d331237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90359 q ha hb
  have h8 (q : Pattern) (ha : d330969 q = 1) (hb : d331238 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d330969, d331238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330969, d331238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d330970 q = 1) (hb : d331239 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d330970, d331239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d330970, d331239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d330971 q = 1) (hb : d331240 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d330971, d331240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d330971, d331240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d331027 q = 1) (hb : d331280 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d331027, d331280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d331027, d331280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90365 q ha hb
  have h12 (q : Pattern) (ha : d331028 q = 1) (hb : d331281 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d331028, d331281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d331028, d331281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d331029 q = 1) (hb : d331282 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d331029, d331282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d331029, d331282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d331030 q = 1) (hb : d331283 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d331030, d331283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d331030, d331283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d331031 q = 1) (hb : d331284 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d331031, d331284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d331031, d331284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d331032 q = 1) (hb : d331285 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d331032, d331285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d331032, d331285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro90367 (p : Pattern) (ha : d331038 p = 1) (hb : d331291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331033 q = 1) (hb : d331286 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d331033, d331286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90366 q ha hb
    | true =>
      simp only [d331033, d331286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d331034 q = 1) (hb : d331287 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d331034, d331287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d331034, d331287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d331035 q = 1) (hb : d331288 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d331035, d331288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d331035, d331288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d331036 q = 1) (hb : d331289 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d331036, d331289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d331036, d331289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d331037 q = 1) (hb : d331290 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d331037, d331290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d331037, d331290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d331038 q = 1) (hb : d331291 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d331038, d331291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d331038, d331291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90368 (p : Pattern) (ha : d331044 p = 1) (hb : d331297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331039 q = 1) (hb : d331292 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d331039, d331292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90367 q ha hb
    | true =>
      simp only [d331039, d331292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d331040 q = 1) (hb : d331293 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d331040, d331293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d331040, d331293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d331041 q = 1) (hb : d331294 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d331041, d331294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d331041, d331294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d331042 q = 1) (hb : d331295 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d331042, d331295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d331042, d331295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d331043 q = 1) (hb : d331296 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d331043, d331296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d331043, d331296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d331044 q = 1) (hb : d331297 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d331044, d331297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d331044, d331297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90369 (p : Pattern) (ha : d331050 p = 1) (hb : d331303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331045 q = 1) (hb : d331298 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d331045, d331298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90368 q ha hb
    | true =>
      simp only [d331045, d331298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d331046 q = 1) (hb : d331299 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d331046, d331299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d331046, d331299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d331047 q = 1) (hb : d331300 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d331047, d331300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d331047, d331300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d331048 q = 1) (hb : d331301 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d331048, d331301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d331048, d331301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d331049 q = 1) (hb : d331302 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d331049, d331302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d331049, d331302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d331050 q = 1) (hb : d331303 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d331050, d331303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d331050, d331303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90370 (p : Pattern) (ha : d331056 p = 1) (hb : d331309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331051 q = 1) (hb : d331304 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d331051, d331304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90369 q ha hb
    | true =>
      simp only [d331051, d331304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d331052 q = 1) (hb : d331305 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d331052, d331305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d331052, d331305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d331053 q = 1) (hb : d331306 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d331053, d331306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d331053, d331306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d331054 q = 1) (hb : d331307 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d331054, d331307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d331054, d331307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d331055 q = 1) (hb : d331308 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d331055, d331308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d331055, d331308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d331056 q = 1) (hb : d331309 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d331056, d331309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d331056, d331309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90371 (p : Pattern) (ha : d331062 p = 1) (hb : d331315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331057 q = 1) (hb : d331310 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d331057, d331310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90370 q ha hb
    | true =>
      simp only [d331057, d331310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d331058 q = 1) (hb : d331311 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d331058, d331311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d331058, d331311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d331059 q = 1) (hb : d331312 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d331059, d331312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d331059, d331312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d331060 q = 1) (hb : d331313 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d331060, d331313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d331060, d331313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d331061 q = 1) (hb : d331314 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d331061, d331314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d331061, d331314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d331062 q = 1) (hb : d331315 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d331062, d331315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d331062, d331315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90372 (p : Pattern) (ha : d331068 p = 1) (hb : d331321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331063 q = 1) (hb : d331316 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d331063, d331316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90371 q ha hb
    | true =>
      simp only [d331063, d331316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d331064 q = 1) (hb : d331317 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d331064, d331317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d331064, d331317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d331065 q = 1) (hb : d331318 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d331065, d331318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d331065, d331318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d331066 q = 1) (hb : d331319 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d331066, d331319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d331066, d331319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d331067 q = 1) (hb : d331320 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d331067, d331320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d331067, d331320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d331068 q = 1) (hb : d331321 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d331068, d331321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d331068, d331321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90373 (p : Pattern) (ha : d331074 p = 1) (hb : d331327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d331069 q = 1) (hb : d331322 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d331069, d331322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90372 q ha hb
    | true =>
      simp only [d331069, d331322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d331070 q = 1) (hb : d331323 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d331070, d331323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d331070, d331323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d331071 q = 1) (hb : d331324 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d331071, d331324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d331071, d331324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d331072 q = 1) (hb : d331325 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d331072, d331325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d331072, d331325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d331073 q = 1) (hb : d331326 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d331073, d331326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d331073, d331326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d331074 q = 1) (hb : d331327 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d331074, d331327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d331074, d331327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90374 (p : Pattern) (ha : d271179 p = 1) (hb : d331330 p = 1) : d326435 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271174 q = 1) (hb : d325306 q = 1) : d326430 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d271174, d326430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88615 q ha hb
    | true =>
      simp only [d271174, d326430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271175 q = 1) (hb : d325306 q = 1) : d326431 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d271175, d326431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271175, d326431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271176 q = 1) (hb : d325306 q = 1) : d326432 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d271176, d326432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271176, d326432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271177 q = 1) (hb : d325306 q = 1) : d326433 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d271177, d326433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271177, d326433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d271178 q = 1) (hb : d331330 q = 1) : d326434 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d271178, d331330, d326434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271178, d331330, d326434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d271179 q = 1) (hb : d331330 q = 1) : d326435 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d271179, d326435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d271179, d326435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90375 (p : Pattern) (ha : d271185 p = 1) (hb : d331330 p = 1) : d326441 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271180 q = 1) (hb : d331330 q = 1) : d326436 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d271180, d326436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90374 q ha hb
    | true =>
      simp only [d271180, d326436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271181 q = 1) (hb : d331330 q = 1) : d326437 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d271181, d326437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271181, d326437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271182 q = 1) (hb : d331330 q = 1) : d326438 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d271182, d326438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271182, d326438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271183 q = 1) (hb : d331330 q = 1) : d326439 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d271183, d326439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271183, d326439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271184 q = 1) (hb : d331330 q = 1) : d326440 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d271184, d326440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271184, d326440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271185 q = 1) (hb : d331330 q = 1) : d326441 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d271185, d326441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271185, d326441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90376 (p : Pattern) (ha : d271191 p = 1) (hb : d331330 p = 1) : d326447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271186 q = 1) (hb : d331330 q = 1) : d326442 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d271186, d326442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90375 q ha hb
    | true =>
      simp only [d271186, d326442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271187 q = 1) (hb : d331330 q = 1) : d326443 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d271187, d326443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271187, d326443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271188 q = 1) (hb : d331330 q = 1) : d326444 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d271188, d326444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271188, d326444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271189 q = 1) (hb : d331330 q = 1) : d326445 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d271189, d326445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271189, d326445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271190 q = 1) (hb : d331330 q = 1) : d326446 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d271190, d326446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271190, d326446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271191 q = 1) (hb : d331330 q = 1) : d326447 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d271191, d326447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271191, d326447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90377 (p : Pattern) (ha : d271197 p = 1) (hb : d331330 p = 1) : d326453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271192 q = 1) (hb : d331330 q = 1) : d326448 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d271192, d326448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90376 q ha hb
    | true =>
      simp only [d271192, d326448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271193 q = 1) (hb : d331330 q = 1) : d326449 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d271193, d326449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271193, d326449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271194 q = 1) (hb : d331330 q = 1) : d326450 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d271194, d326450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271194, d326450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271195 q = 1) (hb : d331330 q = 1) : d326451 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d271195, d326451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271195, d326451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271196 q = 1) (hb : d331330 q = 1) : d326452 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d271196, d326452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271196, d326452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271197 q = 1) (hb : d331330 q = 1) : d326453 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d271197, d326453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271197, d326453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90378 (p : Pattern) (ha : d271203 p = 1) (hb : d331330 p = 1) : d326459 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271198 q = 1) (hb : d331330 q = 1) : d326454 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d271198, d326454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90377 q ha hb
    | true =>
      simp only [d271198, d326454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271199 q = 1) (hb : d331330 q = 1) : d326455 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d271199, d326455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271199, d326455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271200 q = 1) (hb : d331330 q = 1) : d326456 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d271200, d326456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271200, d326456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271201 q = 1) (hb : d331330 q = 1) : d326457 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d271201, d326457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271201, d326457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271202 q = 1) (hb : d331330 q = 1) : d326458 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d271202, d326458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271202, d326458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271203 q = 1) (hb : d331330 q = 1) : d326459 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d271203, d326459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271203, d326459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90379 (p : Pattern) (ha : d271209 p = 1) (hb : d331330 p = 1) : d326465 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271204 q = 1) (hb : d331330 q = 1) : d326460 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d271204, d326460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90378 q ha hb
    | true =>
      simp only [d271204, d326460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d271205 q = 1) (hb : d331330 q = 1) : d326461 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d271205, d326461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d271205, d326461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d271206 q = 1) (hb : d331330 q = 1) : d326462 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d271206, d326462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d271206, d326462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d271207 q = 1) (hb : d331330 q = 1) : d326463 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d271207, d326463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d271207, d326463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271208 q = 1) (hb : d331330 q = 1) : d326464 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d271208, d326464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d271208, d326464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d271209 q = 1) (hb : d331330 q = 1) : d326465 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d271209, d326465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d271209, d326465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90380 (p : Pattern) (ha : d324393 p = 1) (hb : d331330 p = 1) : d326635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d325306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324388 q = 1) (hb : d325306 q = 1) : d326630 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d324388, d326630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88923 q ha hb
    | true =>
      simp only [d324388, d326630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324389 q = 1) (hb : d325306 q = 1) : d326631 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d324389, d326631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324389, d326631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324390 q = 1) (hb : d325306 q = 1) : d326632 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d324390, d326632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324390, d326632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324391 q = 1) (hb : d325306 q = 1) : d326633 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d324391, d326633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324391, d326633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d324392 q = 1) (hb : d331330 q = 1) : d326634 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d324392, d331330, d326634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324392, d331330, d326634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d324393 q = 1) (hb : d331330 q = 1) : d326635 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d324393, d326635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d324393, d326635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90381 (p : Pattern) (ha : d324399 p = 1) (hb : d331330 p = 1) : d326641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324394 q = 1) (hb : d331330 q = 1) : d326636 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d324394, d326636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90380 q ha hb
    | true =>
      simp only [d324394, d326636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324395 q = 1) (hb : d331330 q = 1) : d326637 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d324395, d326637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324395, d326637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324396 q = 1) (hb : d331330 q = 1) : d326638 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d324396, d326638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324396, d326638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324397 q = 1) (hb : d331330 q = 1) : d326639 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d324397, d326639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324397, d326639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324398 q = 1) (hb : d331330 q = 1) : d326640 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d324398, d326640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324398, d326640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324399 q = 1) (hb : d331330 q = 1) : d326641 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d324399, d326641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324399, d326641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90382 (p : Pattern) (ha : d324405 p = 1) (hb : d331330 p = 1) : d326647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324400 q = 1) (hb : d331330 q = 1) : d326642 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d324400, d326642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90381 q ha hb
    | true =>
      simp only [d324400, d326642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324401 q = 1) (hb : d331330 q = 1) : d326643 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d324401, d326643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324401, d326643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324402 q = 1) (hb : d331330 q = 1) : d326644 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d324402, d326644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324402, d326644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324403 q = 1) (hb : d331330 q = 1) : d326645 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d324403, d326645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324403, d326645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324404 q = 1) (hb : d331330 q = 1) : d326646 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d324404, d326646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324404, d326646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324405 q = 1) (hb : d331330 q = 1) : d326647 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d324405, d326647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324405, d326647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90383 (p : Pattern) (ha : d324411 p = 1) (hb : d331330 p = 1) : d326653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324406 q = 1) (hb : d331330 q = 1) : d326648 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d324406, d326648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90382 q ha hb
    | true =>
      simp only [d324406, d326648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324407 q = 1) (hb : d331330 q = 1) : d326649 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d324407, d326649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324407, d326649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324408 q = 1) (hb : d331330 q = 1) : d326650 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d324408, d326650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324408, d326650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324409 q = 1) (hb : d331330 q = 1) : d326651 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d324409, d326651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324409, d326651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324410 q = 1) (hb : d331330 q = 1) : d326652 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d324410, d326652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324410, d326652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324411 q = 1) (hb : d331330 q = 1) : d326653 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d324411, d326653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324411, d326653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90384 (p : Pattern) (ha : d324417 p = 1) (hb : d331330 p = 1) : d326659 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324412 q = 1) (hb : d331330 q = 1) : d326654 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d324412, d326654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90383 q ha hb
    | true =>
      simp only [d324412, d326654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324413 q = 1) (hb : d331330 q = 1) : d326655 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d324413, d326655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324413, d326655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324414 q = 1) (hb : d331330 q = 1) : d326656 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d324414, d326656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324414, d326656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324415 q = 1) (hb : d331330 q = 1) : d326657 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d324415, d326657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324415, d326657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324416 q = 1) (hb : d331330 q = 1) : d326658 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d324416, d326658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324416, d326658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324417 q = 1) (hb : d331330 q = 1) : d326659 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d324417, d326659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324417, d326659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90385 (p : Pattern) (ha : d324423 p = 1) (hb : d331330 p = 1) : d326665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d324418 q = 1) (hb : d331330 q = 1) : d326660 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d324418, d326660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90384 q ha hb
    | true =>
      simp only [d324418, d326660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d324419 q = 1) (hb : d331330 q = 1) : d326661 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d324419, d326661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d324419, d326661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d324420 q = 1) (hb : d331330 q = 1) : d326662 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d324420, d326662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d324420, d326662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d324421 q = 1) (hb : d331330 q = 1) : d326663 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d324421, d326663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d324421, d326663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d324422 q = 1) (hb : d331330 q = 1) : d326664 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d324422, d326664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d324422, d326664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d324423 q = 1) (hb : d331330 q = 1) : d326665 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d324423, d326665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d324423, d326665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90386 (p : Pattern) (ha : d5011 p = 1) (hb : d331335 p = 1) : d331336 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d127 q = 1) : d127 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128 q = 1) (hb : d271213 q = 1) : d308 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d271213, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128, d271213, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d271213 q = 1) : d14 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d129 q = 1) (hb : d271213 q = 1) : d42246 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d42246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129, d42246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d534 q = 1) (hb : d331334 q = 1) : d42598 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d534, d331334, d42598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d534, d331334, d42598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16 q = 1) (hb : d253504 q = 1) : d16 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5010 q = 1) (hb : d331335 q = 1) : d42600 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d5010, d331335, d42600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5010, d331335, d42600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17 q = 1) (hb : d331335 q = 1) : d17 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d5011 q = 1) (hb : d331335 q = 1) : d331336 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d5011, d331336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5011, d331336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro90387 (p : Pattern) (ha : d36007 p = 1) (hb : d331335 p = 1) : d331342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9452 q = 1) (hb : d331335 q = 1) : d331337 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d331337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90386 q ha hb
    | true =>
      simp only [d9452, d331337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9453 q = 1) (hb : d331335 q = 1) : d331338 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d331338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9453, d331338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d331335 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9454 q = 1) (hb : d331335 q = 1) : d331339 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9454, d331339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9454, d331339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21 q = 1) (hb : d331335 q = 1) : d21 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d36005 q = 1) (hb : d331335 q = 1) : d331340 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36005, d331340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36005, d331340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36006 q = 1) (hb : d331335 q = 1) : d331341 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36006, d331341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36006, d331341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23 q = 1) (hb : d331335 q = 1) : d23 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d36007 q = 1) (hb : d331335 q = 1) : d331342 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d36007, d331342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36007, d331342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro90388 (p : Pattern) (ha : d36013 p = 1) (hb : d331335 p = 1) : d331348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36008 q = 1) (hb : d331335 q = 1) : d331343 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36008, d331343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90387 q ha hb
    | true =>
      simp only [d36008, d331343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36009 q = 1) (hb : d331335 q = 1) : d331344 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36009, d331344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36009, d331344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36010 q = 1) (hb : d331335 q = 1) : d331345 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36010, d331345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36010, d331345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36011 q = 1) (hb : d331335 q = 1) : d331346 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36011, d331346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36011, d331346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d331335 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d36012 q = 1) (hb : d331335 q = 1) : d331347 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36012, d331347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36012, d331347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d331335 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d36013 q = 1) (hb : d331335 q = 1) : d331348 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36013, d331348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36013, d331348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90389 (p : Pattern) (ha : d36019 p = 1) (hb : d331335 p = 1) : d331354 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d331335 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36014 q = 1) (hb : d331335 q = 1) : d331349 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36014, d331349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90388 q ha hb
    | true =>
      simp only [d36014, d331349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36015 q = 1) (hb : d331335 q = 1) : d331350 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36015, d331350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36015, d331350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36016 q = 1) (hb : d331335 q = 1) : d331351 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36016, d331351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36016, d331351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d331335 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d36017 q = 1) (hb : d331335 q = 1) : d331352 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36017, d331352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36017, d331352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d331335 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d36018 q = 1) (hb : d331335 q = 1) : d331353 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36018, d331353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36018, d331353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36019 q = 1) (hb : d331335 q = 1) : d331354 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36019, d331354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36019, d331354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro90390 (p : Pattern) (ha : d36025 p = 1) (hb : d331335 p = 1) : d331360 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36020 q = 1) (hb : d331335 q = 1) : d331355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36020, d331355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90389 q ha hb
    | true =>
      simp only [d36020, d331355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36021 q = 1) (hb : d331335 q = 1) : d331356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36021, d331356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36021, d331356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d331335 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36022 q = 1) (hb : d331335 q = 1) : d331357 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36022, d331357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36022, d331357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36023 q = 1) (hb : d331335 q = 1) : d331358 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36023, d331358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36023, d331358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36024 q = 1) (hb : d331335 q = 1) : d331359 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36024, d331359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36024, d331359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36025 q = 1) (hb : d331335 q = 1) : d331360 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36025, d331360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36025, d331360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro90391 (p : Pattern) (ha : d269915 p = 1) (hb : d331335 p = 1) : d331366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d331335 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d331335 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d331335 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36026 q = 1) (hb : d331335 q = 1) : d331361 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36026, d331361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90390 q ha hb
    | true =>
      simp only [d36026, d331361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269911 q = 1) (hb : d331335 q = 1) : d331362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269911, d331362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269911, d331362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d331335 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d269912 q = 1) (hb : d331335 q = 1) : d331363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269912, d331363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269912, d331363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269913 q = 1) (hb : d331335 q = 1) : d331364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269913, d331364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269913, d331364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269914 q = 1) (hb : d331335 q = 1) : d331365 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269914, d331365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269914, d331365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269915 q = 1) (hb : d331335 q = 1) : d331366 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269915, d331366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269915, d331366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro90392 (p : Pattern) (ha : d36032 p = 1) (hb : d331335 p = 1) : d331367 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36020 q = 1) (hb : d331335 q = 1) : d331355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36020, d331355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90389 q ha hb
    | true =>
      simp only [d36020, d331355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36021 q = 1) (hb : d331335 q = 1) : d331356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36021, d331356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36021, d331356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d331335 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36022 q = 1) (hb : d331335 q = 1) : d331357 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36022, d331357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36022, d331357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36023 q = 1) (hb : d331335 q = 1) : d331358 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36023, d331358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36023, d331358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36024 q = 1) (hb : d331335 q = 1) : d331359 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36024, d331359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36024, d331359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36032 q = 1) (hb : d331335 q = 1) : d331367 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36032, d331367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36032, d331367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro90393 (p : Pattern) (ha : d269920 p = 1) (hb : d331335 p = 1) : d331373 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d331335 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d331335 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d331335 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d36026 q = 1) (hb : d331335 q = 1) : d331361 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36026, d331361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90390 q ha hb
    | true =>
      simp only [d36026, d331361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269911 q = 1) (hb : d331335 q = 1) : d331362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269911, d331362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269911, d331362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d331335 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d269912 q = 1) (hb : d331335 q = 1) : d331363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269912, d331363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269912, d331363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269913 q = 1) (hb : d331335 q = 1) : d331364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269913, d331364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269913, d331364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269914 q = 1) (hb : d331335 q = 1) : d331365 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269914, d331365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269914, d331365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d331335 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d331335 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d331335 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d36033 q = 1) (hb : d331335 q = 1) : d331368 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36033, d331368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90392 q ha hb
    | true =>
      simp only [d36033, d331368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269916 q = 1) (hb : d331335 q = 1) : d331369 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269916, d331369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269916, d331369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d331335 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d269917 q = 1) (hb : d331335 q = 1) : d331370 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269917, d331370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269917, d331370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269918 q = 1) (hb : d331335 q = 1) : d331371 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269918, d331371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269918, d331371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d269919 q = 1) (hb : d331335 q = 1) : d331372 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269919, d331372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269919, d331372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d269920 q = 1) (hb : d331335 q = 1) : d331373 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269920, d331373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269920, d331373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro90394 (p : Pattern) (ha : d269927 p = 1) (hb : d331335 p = 1) : d331380 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d331335 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36033 q = 1) (hb : d331335 q = 1) : d331368 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36033, d331368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90392 q ha hb
    | true =>
      simp only [d36033, d331368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269916 q = 1) (hb : d331335 q = 1) : d331369 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269916, d331369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269916, d331369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d331335 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269917 q = 1) (hb : d331335 q = 1) : d331370 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269917, d331370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269917, d331370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269925 q = 1) (hb : d331335 q = 1) : d331378 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269925, d331378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269925, d331378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269926 q = 1) (hb : d331335 q = 1) : d331379 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269926, d331379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269926, d331379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269927 q = 1) (hb : d331335 q = 1) : d331380 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269927, d331380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269927, d331380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90395 (p : Pattern) (ha : d36056 p = 1) (hb : d331335 p = 1) : d331391 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36051 q = 1) (hb : d331335 q = 1) : d331386 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36051, d331386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36051, d331386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90387 q ha hb
  have h2 (q : Pattern) (ha : d36008 q = 1) (hb : d331335 q = 1) : d331343 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36008, d331343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90387 q ha hb
    | true =>
      simp only [d36008, d331343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36052 q = 1) (hb : d331335 q = 1) : d331387 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36052, d331387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36052, d331387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36009 q = 1) (hb : d331335 q = 1) : d331344 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36009, d331344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36009, d331344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36053 q = 1) (hb : d331335 q = 1) : d331388 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36053, d331388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36053, d331388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36054 q = 1) (hb : d331335 q = 1) : d331389 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36054, d331389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36054, d331389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d331335 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d36055 q = 1) (hb : d331335 q = 1) : d331390 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36055, d331390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36055, d331390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d331335 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d36056 q = 1) (hb : d331335 q = 1) : d331391 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36056, d331391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36056, d331391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro90396 (p : Pattern) (ha : d36062 p = 1) (hb : d331335 p = 1) : d331397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d331335 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36057 q = 1) (hb : d331335 q = 1) : d331392 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36057, d331392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90395 q ha hb
    | true =>
      simp only [d36057, d331392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36058 q = 1) (hb : d331335 q = 1) : d331393 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36058, d331393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36058, d331393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36059 q = 1) (hb : d331335 q = 1) : d331394 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36059, d331394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36059, d331394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d331335 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d36060 q = 1) (hb : d331335 q = 1) : d331395 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36060, d331395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36060, d331395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d331335 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d36061 q = 1) (hb : d331335 q = 1) : d331396 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36061, d331396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36061, d331396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36062 q = 1) (hb : d331335 q = 1) : d331397 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36062, d331397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36062, d331397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro90397 (p : Pattern) (ha : d36068 p = 1) (hb : d331335 p = 1) : d331403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36063 q = 1) (hb : d331335 q = 1) : d331398 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36063, d331398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90396 q ha hb
    | true =>
      simp only [d36063, d331398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36064 q = 1) (hb : d331335 q = 1) : d331399 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36064, d331399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36064, d331399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d331335 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36065 q = 1) (hb : d331335 q = 1) : d331400 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36065, d331400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36065, d331400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36066 q = 1) (hb : d331335 q = 1) : d331401 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36066, d331401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36066, d331401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36067 q = 1) (hb : d331335 q = 1) : d331402 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36067, d331402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36067, d331402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36068 q = 1) (hb : d331335 q = 1) : d331403 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36068, d331403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36068, d331403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro90398 (p : Pattern) (ha : d269937 p = 1) (hb : d331335 p = 1) : d331409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d331335 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36069 q = 1) (hb : d331335 q = 1) : d331404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36069, d331404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90397 q ha hb
    | true =>
      simp only [d36069, d331404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d269933 q = 1) (hb : d331335 q = 1) : d331405 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269933, d331405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269933, d331405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d331335 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269934 q = 1) (hb : d331335 q = 1) : d331406 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269934, d331406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269934, d331406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269935 q = 1) (hb : d331335 q = 1) : d331407 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269935, d331407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269935, d331407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269936 q = 1) (hb : d331335 q = 1) : d331408 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269936, d331408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269936, d331408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269937 q = 1) (hb : d331335 q = 1) : d331409 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269937, d331409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269937, d331409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90399 (p : Pattern) (ha : d269943 p = 1) (hb : d331335 p = 1) : d331415 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d331335 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d269921 q = 1) (hb : d331335 q = 1) : d331374 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269921, d331374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90391 q ha hb
    | true =>
      simp only [d269921, d331374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90393 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d331335 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d269922 q = 1) (hb : d331335 q = 1) : d331375 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269922, d331375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269922, d331375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d269923 q = 1) (hb : d331335 q = 1) : d331376 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269923, d331376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d269923, d331376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269924 q = 1) (hb : d331335 q = 1) : d331377 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269924, d331377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269924, d331377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269928 q = 1) (hb : d331335 q = 1) : d331381 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269928, d331381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269928, d331381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90394 q ha hb
  have h8 (q : Pattern) (ha : d269929 q = 1) (hb : d331335 q = 1) : d331382 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269929, d331382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269929, d331382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d269930 q = 1) (hb : d331335 q = 1) : d331383 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269930, d331383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269930, d331383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d269931 q = 1) (hb : d331335 q = 1) : d331384 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269931, d331384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269931, d331384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d269932 q = 1) (hb : d331335 q = 1) : d331385 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269932, d331385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269932, d331385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269938 q = 1) (hb : d331335 q = 1) : d331410 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269938, d331410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269938, d331410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90398 q ha hb
  have h13 (q : Pattern) (ha : d269939 q = 1) (hb : d331335 q = 1) : d331411 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269939, d331411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269939, d331411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d269940 q = 1) (hb : d331335 q = 1) : d331412 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269940, d331412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d269940, d331412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d269941 q = 1) (hb : d331335 q = 1) : d331413 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269941, d331413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269941, d331413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d269942 q = 1) (hb : d331335 q = 1) : d331414 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269942, d331414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269942, d331414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d269943 q = 1) (hb : d331335 q = 1) : d331415 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d269943, d331415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269943, d331415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro90400 (p : Pattern) (ha : d36090 p = 1) (hb : d331335 p = 1) : d331425 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d331335 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36026 q = 1) (hb : d331335 q = 1) : d331361 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36026, d331361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90390 q ha hb
    | true =>
      simp only [d36026, d331361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36086 q = 1) (hb : d331335 q = 1) : d331421 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36086, d331421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36086, d331421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36087 q = 1) (hb : d331335 q = 1) : d331422 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36087, d331422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36087, d331422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36088 q = 1) (hb : d331335 q = 1) : d331423 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36088, d331423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36088, d331423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36089 q = 1) (hb : d331335 q = 1) : d331424 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36089, d331424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36089, d331424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36090 q = 1) (hb : d331335 q = 1) : d331425 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36090, d331425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36090, d331425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro90401 (p : Pattern) (ha : d36097 p = 1) (hb : d331335 p = 1) : d331432 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d331335 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36026 q = 1) (hb : d331335 q = 1) : d331361 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36026, d331361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90390 q ha hb
    | true =>
      simp only [d36026, d331361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36086 q = 1) (hb : d331335 q = 1) : d331421 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36086, d331421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36086, d331421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36087 q = 1) (hb : d331335 q = 1) : d331422 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36087, d331422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36087, d331422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36088 q = 1) (hb : d331335 q = 1) : d331423 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36088, d331423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36088, d331423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36089 q = 1) (hb : d331335 q = 1) : d331424 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36089, d331424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36089, d331424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d331335 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d36033 q = 1) (hb : d331335 q = 1) : d331368 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36033, d331368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90392 q ha hb
    | true =>
      simp only [d36033, d331368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36093 q = 1) (hb : d331335 q = 1) : d331428 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36093, d331428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36093, d331428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36094 q = 1) (hb : d331335 q = 1) : d331429 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36094, d331429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36094, d331429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36095 q = 1) (hb : d331335 q = 1) : d331430 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36095, d331430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36095, d331430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d36096 q = 1) (hb : d331335 q = 1) : d331431 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36096, d331431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36096, d331431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d36097 q = 1) (hb : d331335 q = 1) : d331432 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36097, d331432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36097, d331432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro90402 (p : Pattern) (ha : d36201 p = 1) (hb : d331335 p = 1) : d331513 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d331335 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36026 q = 1) (hb : d331335 q = 1) : d331361 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36026, d331361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90390 q ha hb
    | true =>
      simp only [d36026, d331361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36086 q = 1) (hb : d331335 q = 1) : d331421 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36086, d331421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36086, d331421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36087 q = 1) (hb : d331335 q = 1) : d331422 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36087, d331422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36087, d331422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36088 q = 1) (hb : d331335 q = 1) : d331423 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36088, d331423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36088, d331423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36089 q = 1) (hb : d331335 q = 1) : d331424 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36089, d331424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36089, d331424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d331335 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d36201 q = 1) (hb : d331335 q = 1) : d331513 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36201, d331513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36201, d331513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90403 (p : Pattern) (ha : d36102 p = 1) (hb : d331335 p = 1) : d331437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36020 q = 1) (hb : d331335 q = 1) : d331355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36020, d331355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90389 q ha hb
    | true =>
      simp only [d36020, d331355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36021 q = 1) (hb : d331335 q = 1) : d331356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36021, d331356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36021, d331356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d331335 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36022 q = 1) (hb : d331335 q = 1) : d331357 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36022, d331357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36022, d331357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36023 q = 1) (hb : d331335 q = 1) : d331358 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36023, d331358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36023, d331358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36101 q = 1) (hb : d331335 q = 1) : d331436 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36101, d331436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36101, d331436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36102 q = 1) (hb : d331335 q = 1) : d331437 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36102, d331437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36102, d331437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro90404 (p : Pattern) (ha : d36109 p = 1) (hb : d331335 p = 1) : d331444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36020 q = 1) (hb : d331335 q = 1) : d331355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36020, d331355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90389 q ha hb
    | true =>
      simp only [d36020, d331355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36021 q = 1) (hb : d331335 q = 1) : d331356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36021, d331356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36021, d331356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d331335 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36022 q = 1) (hb : d331335 q = 1) : d331357 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36022, d331357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36022, d331357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36107 q = 1) (hb : d331335 q = 1) : d331442 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36107, d331442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36107, d331442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36108 q = 1) (hb : d331335 q = 1) : d331443 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36108, d331443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36108, d331443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36109 q = 1) (hb : d331335 q = 1) : d331444 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36109, d331444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36109, d331444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro90405 (p : Pattern) (ha : d36114 p = 1) (hb : d331335 p = 1) : d331448 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d307 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d271213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d307, d271213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d271213 q = 1) : d308 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309 q = 1) (hb : d271213 q = 1) : d1523 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, d1523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309, d1523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d825 q = 1) (hb : d331334 q = 1) : d2005 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d825, d331334, d2005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d825, d331334, d2005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d128 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14, d128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14 q = 1) (hb : d14 q = 1) : d14 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d14 q = 1) (hb : d129 q = 1) : d1084 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d129, d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d534 q = 1) (hb : d253504 q = 1) : d1085 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d534, d253504, d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d534, d253504, d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h13 (q : Pattern) (ha : d36113 q = 1) (hb : d331335 q = 1) : d42940 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d36113, d331335, d42940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36113, d331335, d42940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1 q = 1) (hb : d127 q = 1) : d127 q = 1 := by
    exact hb
  have h15 (q : Pattern) (ha : d128 q = 1) (hb : d271213 q = 1) : d308 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d271213, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d128, d271213, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d271213 q = 1) : d14 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d129 q = 1) (hb : d271213 q = 1) : d42246 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d42246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129, d42246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d534 q = 1) (hb : d331334 q = 1) : d42598 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d534, d331334, d42598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d534, d331334, d42598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h19 (q : Pattern) (ha : d16 q = 1) (hb : d253504 q = 1) : d16 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d5010 q = 1) (hb : d331335 q = 1) : d42600 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d5010, d331335, d42600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5010, d331335, d42600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d36114 q = 1) (hb : d331335 q = 1) : d331448 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d36114, d331448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36114, d331448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro90406 (p : Pattern) (ha : d36120 p = 1) (hb : d331335 p = 1) : d331454 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36115 q = 1) (hb : d331335 q = 1) : d331449 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d36115, d331449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90405 q ha hb
    | true =>
      simp only [d36115, d331449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36116 q = 1) (hb : d331335 q = 1) : d331450 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d36116, d331450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36116, d331450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9452 q = 1) (hb : d331335 q = 1) : d331337 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d331337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90386 q ha hb
    | true =>
      simp only [d9452, d331337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9453 q = 1) (hb : d331335 q = 1) : d331338 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d331338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9453, d331338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36117 q = 1) (hb : d331335 q = 1) : d331451 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d36117, d331451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36117, d331451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20 q = 1) (hb : d331335 q = 1) : d20 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9454 q = 1) (hb : d331335 q = 1) : d331339 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9454, d331339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9454, d331339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36118 q = 1) (hb : d331335 q = 1) : d331452 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36118, d331452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36118, d331452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36119 q = 1) (hb : d331335 q = 1) : d331453 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36119, d331453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36119, d331453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21 q = 1) (hb : d331335 q = 1) : d21 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d36005 q = 1) (hb : d331335 q = 1) : d331340 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36005, d331340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36005, d331340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d36006 q = 1) (hb : d331335 q = 1) : d331341 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36006, d331341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36006, d331341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d36120 q = 1) (hb : d331335 q = 1) : d331454 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d36120, d331454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36120, d331454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro90407 (p : Pattern) (ha : d36126 p = 1) (hb : d331335 p = 1) : d331462 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9452 q = 1) (hb : d331335 q = 1) : d331337 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d331337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90386 q ha hb
    | true =>
      simp only [d9452, d331337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9453 q = 1) (hb : d331335 q = 1) : d331338 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d331338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9453, d331338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d331335 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9454 q = 1) (hb : d331335 q = 1) : d331339 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9454, d331339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9454, d331339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9455 q = 1) (hb : d331335 q = 1) : d331460 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9455, d331460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9455, d331460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9456 q = 1) (hb : d331335 q = 1) : d331461 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9456, d331461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9456, d331461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23 q = 1) (hb : d331335 q = 1) : d23 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d36126 q = 1) (hb : d331335 q = 1) : d331462 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d36126, d331462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36126, d331462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90408 (p : Pattern) (ha : d36132 p = 1) (hb : d331335 p = 1) : d331468 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36121 q = 1) (hb : d331335 q = 1) : d331455 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36121, d331455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90406 q ha hb
    | true =>
      simp only [d36121, d331455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36122 q = 1) (hb : d331335 q = 1) : d331456 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36122, d331456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36122, d331456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36123 q = 1) (hb : d331335 q = 1) : d331457 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36123, d331457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36123, d331457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36124 q = 1) (hb : d331335 q = 1) : d331458 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36124, d331458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36124, d331458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36008 q = 1) (hb : d331335 q = 1) : d331343 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36008, d331343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90387 q ha hb
    | true =>
      simp only [d36008, d331343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36009 q = 1) (hb : d331335 q = 1) : d331344 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36009, d331344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36009, d331344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36010 q = 1) (hb : d331335 q = 1) : d331345 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36010, d331345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36010, d331345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36011 q = 1) (hb : d331335 q = 1) : d331346 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36011, d331346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36011, d331346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36125 q = 1) (hb : d331335 q = 1) : d331459 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36125, d331459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36125, d331459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36127 q = 1) (hb : d331335 q = 1) : d331463 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36127, d331463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90407 q ha hb
    | true =>
      simp only [d36127, d331463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36128 q = 1) (hb : d331335 q = 1) : d331464 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36128, d331464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36128, d331464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d36129 q = 1) (hb : d331335 q = 1) : d331465 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36129, d331465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36129, d331465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d36130 q = 1) (hb : d331335 q = 1) : d331466 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36130, d331466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d36130, d331466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28 q = 1) (hb : d331335 q = 1) : d28 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d36131 q = 1) (hb : d331335 q = 1) : d331467 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36131, d331467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36131, d331467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d36132 q = 1) (hb : d331335 q = 1) : d331468 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36132, d331468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36132, d331468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro90409 (p : Pattern) (ha : d36138 p = 1) (hb : d331335 p = 1) : d331474 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36133 q = 1) (hb : d331335 q = 1) : d331469 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36133, d331469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90408 q ha hb
    | true =>
      simp only [d36133, d331469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90388 q ha hb
  have h2 (q : Pattern) (ha : d36134 q = 1) (hb : d331335 q = 1) : d331470 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36134, d331470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36134, d331470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36135 q = 1) (hb : d331335 q = 1) : d331471 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36135, d331471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36135, d331471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d331335 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d36014 q = 1) (hb : d331335 q = 1) : d331349 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36014, d331349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90388 q ha hb
    | true =>
      simp only [d36014, d331349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36015 q = 1) (hb : d331335 q = 1) : d331350 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36015, d331350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36015, d331350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36016 q = 1) (hb : d331335 q = 1) : d331351 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36016, d331351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36016, d331351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36136 q = 1) (hb : d331335 q = 1) : d331472 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36136, d331472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36136, d331472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d331335 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d36017 q = 1) (hb : d331335 q = 1) : d331352 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36017, d331352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36017, d331352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36137 q = 1) (hb : d331335 q = 1) : d331473 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36137, d331473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36137, d331473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d36138 q = 1) (hb : d331335 q = 1) : d331474 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36138, d331474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36138, d331474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro90410 (p : Pattern) (ha : d36144 p = 1) (hb : d331335 p = 1) : d331480 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36139 q = 1) (hb : d331335 q = 1) : d331475 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36139, d331475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90409 q ha hb
    | true =>
      simp only [d36139, d331475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36140 q = 1) (hb : d331335 q = 1) : d331476 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36140, d331476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36140, d331476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36020 q = 1) (hb : d331335 q = 1) : d331355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36020, d331355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90389 q ha hb
    | true =>
      simp only [d36020, d331355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36021 q = 1) (hb : d331335 q = 1) : d331356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36021, d331356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36021, d331356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36141 q = 1) (hb : d331335 q = 1) : d331477 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36141, d331477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36141, d331477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36142 q = 1) (hb : d331335 q = 1) : d331478 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36142, d331478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36142, d331478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36143 q = 1) (hb : d331335 q = 1) : d331479 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36143, d331479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36143, d331479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36144 q = 1) (hb : d331335 q = 1) : d331480 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36144, d331480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36144, d331480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90411 (p : Pattern) (ha : d36172 p = 1) (hb : d331335 p = 1) : d331486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36020 q = 1) (hb : d331335 q = 1) : d331355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36020, d331355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90389 q ha hb
    | true =>
      simp only [d36020, d331355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36021 q = 1) (hb : d331335 q = 1) : d331356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36021, d331356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36021, d331356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36169 q = 1) (hb : d331335 q = 1) : d331483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36169, d331483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36169, d331483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36170 q = 1) (hb : d331335 q = 1) : d331484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36170, d331484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36170, d331484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36171 q = 1) (hb : d331335 q = 1) : d331485 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36171, d331485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36171, d331485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36172 q = 1) (hb : d331335 q = 1) : d331486 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36172, d331486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36172, d331486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90412 (p : Pattern) (ha : d269953 p = 1) (hb : d331335 p = 1) : d331492 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d331335 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36103 q = 1) (hb : d331335 q = 1) : d331438 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36103, d331438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90403 q ha hb
    | true =>
      simp only [d36103, d331438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36104 q = 1) (hb : d331335 q = 1) : d331439 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36104, d331439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36104, d331439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36105 q = 1) (hb : d331335 q = 1) : d331440 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36105, d331440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36105, d331440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36106 q = 1) (hb : d331335 q = 1) : d331441 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36106, d331441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36106, d331441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d331335 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d36110 q = 1) (hb : d331335 q = 1) : d331445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36110, d331445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90404 q ha hb
    | true =>
      simp only [d36110, d331445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36111 q = 1) (hb : d331335 q = 1) : d331446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36111, d331446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36111, d331446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36112 q = 1) (hb : d331335 q = 1) : d331447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36112, d331447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36112, d331447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d36145 q = 1) (hb : d331335 q = 1) : d331481 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36145, d331481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90410 q ha hb
    | true =>
      simp only [d36145, d331481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90390 q ha hb
  have h11 (q : Pattern) (ha : d269949 q = 1) (hb : d331335 q = 1) : d331482 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269949, d331482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269949, d331482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d36173 q = 1) (hb : d331335 q = 1) : d331487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36173, d331487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90411 q ha hb
    | true =>
      simp only [d36173, d331487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d36174 q = 1) (hb : d331335 q = 1) : d331488 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36174, d331488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d36174, d331488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d269950 q = 1) (hb : d331335 q = 1) : d331489 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269950, d331489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269950, d331489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269951 q = 1) (hb : d331335 q = 1) : d331490 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269951, d331490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269951, d331490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269952 q = 1) (hb : d331335 q = 1) : d331491 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269952, d331491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269952, d331491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d269953 q = 1) (hb : d331335 q = 1) : d331492 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269953, d331492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269953, d331492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro90413 (p : Pattern) (ha : d36179 p = 1) (hb : d331335 p = 1) : d331493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36020 q = 1) (hb : d331335 q = 1) : d331355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36020, d331355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90389 q ha hb
    | true =>
      simp only [d36020, d331355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36021 q = 1) (hb : d331335 q = 1) : d331356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36021, d331356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36021, d331356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d331335 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36022 q = 1) (hb : d331335 q = 1) : d331357 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36022, d331357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36022, d331357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36023 q = 1) (hb : d331335 q = 1) : d331358 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36023, d331358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36023, d331358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36101 q = 1) (hb : d331335 q = 1) : d331436 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36101, d331436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36101, d331436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36179 q = 1) (hb : d331335 q = 1) : d331493 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36179, d331493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36179, d331493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro90414 (p : Pattern) (ha : d36184 p = 1) (hb : d331335 p = 1) : d331498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36020 q = 1) (hb : d331335 q = 1) : d331355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36020, d331355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90389 q ha hb
    | true =>
      simp only [d36020, d331355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36021 q = 1) (hb : d331335 q = 1) : d331356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36021, d331356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36021, d331356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d331335 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d36022 q = 1) (hb : d331335 q = 1) : d331357 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36022, d331357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36022, d331357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36107 q = 1) (hb : d331335 q = 1) : d331442 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36107, d331442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36107, d331442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36108 q = 1) (hb : d331335 q = 1) : d331443 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36108, d331443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36108, d331443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36184 q = 1) (hb : d331335 q = 1) : d331498 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36184, d331498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36184, d331498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro90415 (p : Pattern) (ha : d36188 p = 1) (hb : d331335 p = 1) : d331502 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36139 q = 1) (hb : d331335 q = 1) : d331475 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36139, d331475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90409 q ha hb
    | true =>
      simp only [d36139, d331475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36140 q = 1) (hb : d331335 q = 1) : d331476 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36140, d331476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36140, d331476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36020 q = 1) (hb : d331335 q = 1) : d331355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36020, d331355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90389 q ha hb
    | true =>
      simp only [d36020, d331355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36021 q = 1) (hb : d331335 q = 1) : d331356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36021, d331356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36021, d331356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36141 q = 1) (hb : d331335 q = 1) : d331477 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36141, d331477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36141, d331477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36142 q = 1) (hb : d331335 q = 1) : d331478 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36142, d331478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36142, d331478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36143 q = 1) (hb : d331335 q = 1) : d331479 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36143, d331479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36143, d331479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36188 q = 1) (hb : d331335 q = 1) : d331502 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36188, d331502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36188, d331502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro90416 (p : Pattern) (ha : d36193 p = 1) (hb : d331335 p = 1) : d331505 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36020 q = 1) (hb : d331335 q = 1) : d331355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36020, d331355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90389 q ha hb
    | true =>
      simp only [d36020, d331355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36021 q = 1) (hb : d331335 q = 1) : d331356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36021, d331356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36021, d331356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36169 q = 1) (hb : d331335 q = 1) : d331483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36169, d331483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36169, d331483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36170 q = 1) (hb : d331335 q = 1) : d331484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36170, d331484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36170, d331484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36171 q = 1) (hb : d331335 q = 1) : d331485 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36171, d331485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36171, d331485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36193 q = 1) (hb : d331335 q = 1) : d331505 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36193, d331505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36193, d331505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90417 (p : Pattern) (ha : d269958 p = 1) (hb : d331335 p = 1) : d331511 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d331335 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36103 q = 1) (hb : d331335 q = 1) : d331438 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36103, d331438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90403 q ha hb
    | true =>
      simp only [d36103, d331438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36104 q = 1) (hb : d331335 q = 1) : d331439 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36104, d331439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36104, d331439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36105 q = 1) (hb : d331335 q = 1) : d331440 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36105, d331440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36105, d331440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36106 q = 1) (hb : d331335 q = 1) : d331441 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36106, d331441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36106, d331441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d331335 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d36110 q = 1) (hb : d331335 q = 1) : d331445 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36110, d331445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90404 q ha hb
    | true =>
      simp only [d36110, d331445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36111 q = 1) (hb : d331335 q = 1) : d331446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36111, d331446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36111, d331446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36112 q = 1) (hb : d331335 q = 1) : d331447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36112, d331447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36112, d331447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d36145 q = 1) (hb : d331335 q = 1) : d331481 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36145, d331481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90410 q ha hb
    | true =>
      simp only [d36145, d331481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90390 q ha hb
  have h11 (q : Pattern) (ha : d269949 q = 1) (hb : d331335 q = 1) : d331482 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269949, d331482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d269949, d331482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d36173 q = 1) (hb : d331335 q = 1) : d331487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36173, d331487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90411 q ha hb
    | true =>
      simp only [d36173, d331487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d36174 q = 1) (hb : d331335 q = 1) : d331488 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36174, d331488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d36174, d331488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d269950 q = 1) (hb : d331335 q = 1) : d331489 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269950, d331489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269950, d331489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269951 q = 1) (hb : d331335 q = 1) : d331490 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269951, d331490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269951, d331490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d269952 q = 1) (hb : d331335 q = 1) : d331491 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269952, d331491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269952, d331491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d331335 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d36180 q = 1) (hb : d331335 q = 1) : d331494 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36180, d331494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90413 q ha hb
    | true =>
      simp only [d36180, d331494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d36181 q = 1) (hb : d331335 q = 1) : d331495 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36181, d331495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36181, d331495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d36182 q = 1) (hb : d331335 q = 1) : d331496 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36182, d331496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d36182, d331496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d36183 q = 1) (hb : d331335 q = 1) : d331497 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36183, d331497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36183, d331497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d331335 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d36185 q = 1) (hb : d331335 q = 1) : d331499 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36185, d331499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90414 q ha hb
    | true =>
      simp only [d36185, d331499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d36186 q = 1) (hb : d331335 q = 1) : d331500 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36186, d331500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36186, d331500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d36187 q = 1) (hb : d331335 q = 1) : d331501 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36187, d331501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d36187, d331501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d36189 q = 1) (hb : d331335 q = 1) : d331503 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36189, d331503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90415 q ha hb
    | true =>
      simp only [d36189, d331503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90392 q ha hb
  have h27 (q : Pattern) (ha : d269954 q = 1) (hb : d331335 q = 1) : d331504 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269954, d331504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d269954, d331504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d36194 q = 1) (hb : d331335 q = 1) : d331506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36194, d331506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90416 q ha hb
    | true =>
      simp only [d36194, d331506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d36195 q = 1) (hb : d331335 q = 1) : d331507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36195, d331507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d36195, d331507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d269955 q = 1) (hb : d331335 q = 1) : d331508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269955, d331508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d269955, d331508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d269956 q = 1) (hb : d331335 q = 1) : d331509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269956, d331509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d269956, d331509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d269957 q = 1) (hb : d331335 q = 1) : d331510 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269957, d331510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d269957, d331510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d269958 q = 1) (hb : d331335 q = 1) : d331511 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269958, d331511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d269958, d331511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro90418 (p : Pattern) (ha : d269965 p = 1) (hb : d331335 p = 1) : d331520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36189 q = 1) (hb : d331335 q = 1) : d331503 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36189, d331503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90415 q ha hb
    | true =>
      simp only [d36189, d331503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90392 q ha hb
  have h2 (q : Pattern) (ha : d269954 q = 1) (hb : d331335 q = 1) : d331504 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269954, d331504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269954, d331504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36194 q = 1) (hb : d331335 q = 1) : d331506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36194, d331506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90416 q ha hb
    | true =>
      simp only [d36194, d331506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36195 q = 1) (hb : d331335 q = 1) : d331507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36195, d331507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36195, d331507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d269955 q = 1) (hb : d331335 q = 1) : d331508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269955, d331508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269955, d331508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269963 q = 1) (hb : d331335 q = 1) : d331518 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269963, d331518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269963, d331518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269964 q = 1) (hb : d331335 q = 1) : d331519 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269964, d331519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269964, d331519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269965 q = 1) (hb : d331335 q = 1) : d331520 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269965, d331520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269965, d331520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90419 (p : Pattern) (ha : d36224 p = 1) (hb : d331335 p = 1) : d331536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36214 q = 1) (hb : d331335 q = 1) : d331526 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36214, d331526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36214, d331526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90406 q ha hb
  have h2 (q : Pattern) (ha : d36121 q = 1) (hb : d331335 q = 1) : d331455 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36121, d331455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90406 q ha hb
    | true =>
      simp only [d36121, d331455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36215 q = 1) (hb : d331335 q = 1) : d331527 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36215, d331527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36215, d331527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36122 q = 1) (hb : d331335 q = 1) : d331456 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36122, d331456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36122, d331456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36216 q = 1) (hb : d331335 q = 1) : d331528 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36216, d331528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36216, d331528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36217 q = 1) (hb : d331335 q = 1) : d331529 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36217, d331529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36217, d331529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36051 q = 1) (hb : d331335 q = 1) : d331386 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36051, d331386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36051, d331386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90387 q ha hb
  have h8 (q : Pattern) (ha : d36008 q = 1) (hb : d331335 q = 1) : d331343 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36008, d331343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90387 q ha hb
    | true =>
      simp only [d36008, d331343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36052 q = 1) (hb : d331335 q = 1) : d331387 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36052, d331387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36052, d331387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36009 q = 1) (hb : d331335 q = 1) : d331344 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36009, d331344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36009, d331344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36053 q = 1) (hb : d331335 q = 1) : d331388 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36053, d331388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36053, d331388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d36054 q = 1) (hb : d331335 q = 1) : d331389 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36054, d331389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36054, d331389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d36218 q = 1) (hb : d331335 q = 1) : d331530 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36218, d331530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36218, d331530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d36219 q = 1) (hb : d331335 q = 1) : d331531 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36219, d331531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36219, d331531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90407 q ha hb
  have h15 (q : Pattern) (ha : d36127 q = 1) (hb : d331335 q = 1) : d331463 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36127, d331463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90407 q ha hb
    | true =>
      simp only [d36127, d331463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d36220 q = 1) (hb : d331335 q = 1) : d331532 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36220, d331532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d36220, d331532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36128 q = 1) (hb : d331335 q = 1) : d331464 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36128, d331464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d36128, d331464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d36221 q = 1) (hb : d331335 q = 1) : d331533 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36221, d331533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d36221, d331533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d36222 q = 1) (hb : d331335 q = 1) : d331534 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36222, d331534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d36222, d331534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d69 q = 1) (hb : d331335 q = 1) : d69 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d36223 q = 1) (hb : d331335 q = 1) : d331535 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36223, d331535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d36223, d331535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d36224 q = 1) (hb : d331335 q = 1) : d331536 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36224, d331536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36224, d331536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro90420 (p : Pattern) (ha : d36230 p = 1) (hb : d331335 p = 1) : d331542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36225 q = 1) (hb : d331335 q = 1) : d331537 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36225, d331537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90419 q ha hb
    | true =>
      simp only [d36225, d331537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90395 q ha hb
  have h2 (q : Pattern) (ha : d36226 q = 1) (hb : d331335 q = 1) : d331538 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36226, d331538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36226, d331538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36227 q = 1) (hb : d331335 q = 1) : d331539 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36227, d331539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36227, d331539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d331335 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d36057 q = 1) (hb : d331335 q = 1) : d331392 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36057, d331392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90395 q ha hb
    | true =>
      simp only [d36057, d331392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36058 q = 1) (hb : d331335 q = 1) : d331393 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36058, d331393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36058, d331393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36059 q = 1) (hb : d331335 q = 1) : d331394 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36059, d331394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36059, d331394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36228 q = 1) (hb : d331335 q = 1) : d331540 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36228, d331540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36228, d331540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d331335 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d36060 q = 1) (hb : d331335 q = 1) : d331395 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36060, d331395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36060, d331395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36229 q = 1) (hb : d331335 q = 1) : d331541 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36229, d331541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36229, d331541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d36230 q = 1) (hb : d331335 q = 1) : d331542 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36230, d331542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36230, d331542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro90421 (p : Pattern) (ha : d36236 p = 1) (hb : d331335 p = 1) : d331548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36231 q = 1) (hb : d331335 q = 1) : d331543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36231, d331543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90420 q ha hb
    | true =>
      simp only [d36231, d331543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36232 q = 1) (hb : d331335 q = 1) : d331544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36232, d331544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36232, d331544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36063 q = 1) (hb : d331335 q = 1) : d331398 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36063, d331398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90396 q ha hb
    | true =>
      simp only [d36063, d331398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36064 q = 1) (hb : d331335 q = 1) : d331399 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36064, d331399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36064, d331399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36233 q = 1) (hb : d331335 q = 1) : d331545 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36233, d331545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36233, d331545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36234 q = 1) (hb : d331335 q = 1) : d331546 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36234, d331546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36234, d331546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36235 q = 1) (hb : d331335 q = 1) : d331547 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36235, d331547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36235, d331547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36236 q = 1) (hb : d331335 q = 1) : d331548 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36236, d331548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36236, d331548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro90422 (p : Pattern) (ha : d36261 p = 1) (hb : d331335 p = 1) : d331554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36063 q = 1) (hb : d331335 q = 1) : d331398 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36063, d331398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90396 q ha hb
    | true =>
      simp only [d36063, d331398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36064 q = 1) (hb : d331335 q = 1) : d331399 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36064, d331399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36064, d331399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36258 q = 1) (hb : d331335 q = 1) : d331551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36258, d331551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36258, d331551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36259 q = 1) (hb : d331335 q = 1) : d331552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36259, d331552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36259, d331552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36260 q = 1) (hb : d331335 q = 1) : d331553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36260, d331553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36260, d331553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36261 q = 1) (hb : d331335 q = 1) : d331554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36261, d331554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36261, d331554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90423 (p : Pattern) (ha : d269975 p = 1) (hb : d331335 p = 1) : d331560 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36237 q = 1) (hb : d331335 q = 1) : d331549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36237, d331549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90421 q ha hb
    | true =>
      simp only [d36237, d331549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90397 q ha hb
  have h2 (q : Pattern) (ha : d269971 q = 1) (hb : d331335 q = 1) : d331550 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269971, d331550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269971, d331550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36262 q = 1) (hb : d331335 q = 1) : d331555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36262, d331555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90422 q ha hb
    | true =>
      simp only [d36262, d331555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36263 q = 1) (hb : d331335 q = 1) : d331556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36263, d331556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36263, d331556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d269972 q = 1) (hb : d331335 q = 1) : d331557 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269972, d331557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269972, d331557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269973 q = 1) (hb : d331335 q = 1) : d331558 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269973, d331558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269973, d331558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269974 q = 1) (hb : d331335 q = 1) : d331559 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269974, d331559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269974, d331559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d269975 q = 1) (hb : d331335 q = 1) : d331560 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269975, d331560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269975, d331560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90424 (p : Pattern) (ha : d269981 p = 1) (hb : d331335 p = 1) : d331566 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36091 q = 1) (hb : d331335 q = 1) : d331426 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36091, d331426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36091, d331426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90400 q ha hb
  have h2 (q : Pattern) (ha : d36092 q = 1) (hb : d331335 q = 1) : d331427 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36092, d331427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36092, d331427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36098 q = 1) (hb : d331335 q = 1) : d331433 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36098, d331433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90400 q ha hb
    | true =>
      simp only [d36098, d331433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90401 q ha hb
  have h4 (q : Pattern) (ha : d36099 q = 1) (hb : d331335 q = 1) : d331434 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36099, d331434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36099, d331434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36100 q = 1) (hb : d331335 q = 1) : d331435 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d36100, d331435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36100, d331435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269959 q = 1) (hb : d331335 q = 1) : d331512 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269959, d331512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90412 q ha hb
    | true =>
      simp only [d269959, d331512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90417 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d331335 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d36202 q = 1) (hb : d331335 q = 1) : d331514 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36202, d331514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90402 q ha hb
    | true =>
      simp only [d36202, d331514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269960 q = 1) (hb : d331335 q = 1) : d331515 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269960, d331515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269960, d331515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269961 q = 1) (hb : d331335 q = 1) : d331516 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269961, d331516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269961, d331516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d269962 q = 1) (hb : d331335 q = 1) : d331517 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269962, d331517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d269962, d331517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269966 q = 1) (hb : d331335 q = 1) : d331521 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269966, d331521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269966, d331521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90418 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d331335 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d269967 q = 1) (hb : d331335 q = 1) : d331522 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269967, d331522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d269967, d331522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269968 q = 1) (hb : d331335 q = 1) : d331523 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269968, d331523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269968, d331523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d269969 q = 1) (hb : d331335 q = 1) : d331524 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269969, d331524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d269969, d331524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d269970 q = 1) (hb : d331335 q = 1) : d331525 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269970, d331525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d269970, d331525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d269976 q = 1) (hb : d331335 q = 1) : d331561 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269976, d331561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269976, d331561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90423 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d331335 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d269977 q = 1) (hb : d331335 q = 1) : d331562 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269977, d331562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d269977, d331562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d269978 q = 1) (hb : d331335 q = 1) : d331563 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d269978, d331563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d269978, d331563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d269979 q = 1) (hb : d331335 q = 1) : d331564 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d269979, d331564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d269979, d331564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d269980 q = 1) (hb : d331335 q = 1) : d331565 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d269980, d331565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d269980, d331565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d269981 q = 1) (hb : d331335 q = 1) : d331566 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d269981, d331566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d269981, d331566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro90425 (p : Pattern) (ha : d269987 p = 1) (hb : d331335 p = 1) : d331572 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d331335 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d269944 q = 1) (hb : d331335 q = 1) : d331416 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d269944, d331416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269944, d331416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90399 q ha hb
  have h3 (q : Pattern) (ha : d269945 q = 1) (hb : d331335 q = 1) : d331417 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d269945, d331417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269945, d331417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d269946 q = 1) (hb : d331335 q = 1) : d331418 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d269946, d331418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269946, d331418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d269947 q = 1) (hb : d331335 q = 1) : d331419 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d269947, d331419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269947, d331419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269948 q = 1) (hb : d331335 q = 1) : d331420 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d269948, d331420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269948, d331420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d269982 q = 1) (hb : d331335 q = 1) : d331567 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d269982, d331567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269982, d331567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90424 q ha hb
  have h8 (q : Pattern) (ha : d269983 q = 1) (hb : d331335 q = 1) : d331568 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d269983, d331568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269983, d331568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d269984 q = 1) (hb : d331335 q = 1) : d331569 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d269984, d331569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269984, d331569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d269985 q = 1) (hb : d331335 q = 1) : d331570 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d269985, d331570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269985, d331570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d269986 q = 1) (hb : d331335 q = 1) : d331571 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d269986, d331571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269986, d331571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d269987 q = 1) (hb : d331335 q = 1) : d331572 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d269987, d331572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269987, d331572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro90426 (p : Pattern) (ha : d36282 p = 1) (hb : d331335 p = 1) : d331575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36133 q = 1) (hb : d331335 q = 1) : d331469 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36133, d331469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90408 q ha hb
    | true =>
      simp only [d36133, d331469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90388 q ha hb
  have h2 (q : Pattern) (ha : d36134 q = 1) (hb : d331335 q = 1) : d331470 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36134, d331470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36134, d331470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36135 q = 1) (hb : d331335 q = 1) : d331471 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36135, d331471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36135, d331471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d331335 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d36014 q = 1) (hb : d331335 q = 1) : d331349 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36014, d331349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90388 q ha hb
    | true =>
      simp only [d36014, d331349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36015 q = 1) (hb : d331335 q = 1) : d331350 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36015, d331350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36015, d331350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36016 q = 1) (hb : d331335 q = 1) : d331351 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36016, d331351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36016, d331351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36136 q = 1) (hb : d331335 q = 1) : d331472 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36136, d331472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36136, d331472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36280 q = 1) (hb : d331335 q = 1) : d331573 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36280, d331573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36280, d331573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d36281 q = 1) (hb : d331335 q = 1) : d331574 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36281, d331574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36281, d331574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36282 q = 1) (hb : d331335 q = 1) : d331575 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36282, d331575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36282, d331575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro90427 (p : Pattern) (ha : d36286 p = 1) (hb : d331335 p = 1) : d331579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d331335 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36014 q = 1) (hb : d331335 q = 1) : d331349 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36014, d331349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90388 q ha hb
    | true =>
      simp only [d36014, d331349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36015 q = 1) (hb : d331335 q = 1) : d331350 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36015, d331350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36015, d331350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36016 q = 1) (hb : d331335 q = 1) : d331351 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36016, d331351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36016, d331351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36280 q = 1) (hb : d331335 q = 1) : d331573 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36280, d331573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36280, d331573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36285 q = 1) (hb : d331335 q = 1) : d331578 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36285, d331578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36285, d331578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36286 q = 1) (hb : d331335 q = 1) : d331579 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36286, d331579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36286, d331579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro90428 (p : Pattern) (ha : d36292 p = 1) (hb : d331335 p = 1) : d331585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36283 q = 1) (hb : d331335 q = 1) : d331576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36283, d331576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90426 q ha hb
    | true =>
      simp only [d36283, d331576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36284 q = 1) (hb : d331335 q = 1) : d331577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36284, d331577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36284, d331577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36287 q = 1) (hb : d331335 q = 1) : d331580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90427 q ha hb
    | true =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36288 q = 1) (hb : d331335 q = 1) : d331581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36289 q = 1) (hb : d331335 q = 1) : d331582 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36289, d331582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36289, d331582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36290 q = 1) (hb : d331335 q = 1) : d331583 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36290, d331583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36290, d331583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36291 q = 1) (hb : d331335 q = 1) : d331584 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36291, d331584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36291, d331584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36292 q = 1) (hb : d331335 q = 1) : d331585 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36292, d331585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36292, d331585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90429 (p : Pattern) (ha : d36296 p = 1) (hb : d331335 p = 1) : d331589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36287 q = 1) (hb : d331335 q = 1) : d331580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90427 q ha hb
    | true =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36288 q = 1) (hb : d331335 q = 1) : d331581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36293 q = 1) (hb : d331335 q = 1) : d331586 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36293, d331586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36293, d331586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36294 q = 1) (hb : d331335 q = 1) : d331587 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36294, d331587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36294, d331587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36295 q = 1) (hb : d331335 q = 1) : d331588 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36295, d331588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36295, d331588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36296 q = 1) (hb : d331335 q = 1) : d331589 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36296, d331589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36296, d331589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90430 (p : Pattern) (ha : d36302 p = 1) (hb : d331335 p = 1) : d331595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36297 q = 1) (hb : d331335 q = 1) : d331590 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36297, d331590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90428 q ha hb
    | true =>
      simp only [d36297, d331590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90429 q ha hb
  have h2 (q : Pattern) (ha : d36298 q = 1) (hb : d331335 q = 1) : d331591 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36298, d331591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36298, d331591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36299 q = 1) (hb : d331335 q = 1) : d331592 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36299, d331592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36299, d331592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36300 q = 1) (hb : d331335 q = 1) : d331593 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36300, d331593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36300, d331593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36301 q = 1) (hb : d331335 q = 1) : d331594 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36301, d331594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36301, d331594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36302 q = 1) (hb : d331335 q = 1) : d331595 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36302, d331595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36302, d331595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90431 (p : Pattern) (ha : d36305 p = 1) (hb : d331335 p = 1) : d331598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36283 q = 1) (hb : d331335 q = 1) : d331576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36283, d331576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90426 q ha hb
    | true =>
      simp only [d36283, d331576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36284 q = 1) (hb : d331335 q = 1) : d331577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36284, d331577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36284, d331577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36287 q = 1) (hb : d331335 q = 1) : d331580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90427 q ha hb
    | true =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36288 q = 1) (hb : d331335 q = 1) : d331581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36289 q = 1) (hb : d331335 q = 1) : d331582 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36289, d331582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36289, d331582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36290 q = 1) (hb : d331335 q = 1) : d331583 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36290, d331583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36290, d331583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36291 q = 1) (hb : d331335 q = 1) : d331584 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36291, d331584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36291, d331584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36305 q = 1) (hb : d331335 q = 1) : d331598 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36305, d331598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36305, d331598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro90432 (p : Pattern) (ha : d36306 p = 1) (hb : d331335 p = 1) : d331599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36287 q = 1) (hb : d331335 q = 1) : d331580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90427 q ha hb
    | true =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36288 q = 1) (hb : d331335 q = 1) : d331581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36293 q = 1) (hb : d331335 q = 1) : d331586 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36293, d331586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36293, d331586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36294 q = 1) (hb : d331335 q = 1) : d331587 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36294, d331587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36294, d331587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36295 q = 1) (hb : d331335 q = 1) : d331588 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36295, d331588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36295, d331588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36306 q = 1) (hb : d331335 q = 1) : d331599 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36306, d331599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36306, d331599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90433 (p : Pattern) (ha : d36312 p = 1) (hb : d331335 p = 1) : d331605 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36297 q = 1) (hb : d331335 q = 1) : d331590 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36297, d331590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90428 q ha hb
    | true =>
      simp only [d36297, d331590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90429 q ha hb
  have h2 (q : Pattern) (ha : d36298 q = 1) (hb : d331335 q = 1) : d331591 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36298, d331591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36298, d331591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36299 q = 1) (hb : d331335 q = 1) : d331592 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36299, d331592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36299, d331592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36300 q = 1) (hb : d331335 q = 1) : d331593 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36300, d331593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36300, d331593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36301 q = 1) (hb : d331335 q = 1) : d331594 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36301, d331594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36301, d331594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36307 q = 1) (hb : d331335 q = 1) : d331600 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36307, d331600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90431 q ha hb
    | true =>
      simp only [d36307, d331600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90432 q ha hb
  have h7 (q : Pattern) (ha : d36308 q = 1) (hb : d331335 q = 1) : d331601 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36308, d331601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36308, d331601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36309 q = 1) (hb : d331335 q = 1) : d331602 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36309, d331602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36309, d331602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36310 q = 1) (hb : d331335 q = 1) : d331603 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36310, d331603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36310, d331603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36311 q = 1) (hb : d331335 q = 1) : d331604 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36311, d331604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36311, d331604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36312 q = 1) (hb : d331335 q = 1) : d331605 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36312, d331605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36312, d331605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro90434 (p : Pattern) (ha : d36460 p = 1) (hb : d331335 p = 1) : d331704 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36297 q = 1) (hb : d331335 q = 1) : d331590 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36297, d331590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90428 q ha hb
    | true =>
      simp only [d36297, d331590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90429 q ha hb
  have h2 (q : Pattern) (ha : d36298 q = 1) (hb : d331335 q = 1) : d331591 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36298, d331591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36298, d331591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36299 q = 1) (hb : d331335 q = 1) : d331592 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36299, d331592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36299, d331592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36300 q = 1) (hb : d331335 q = 1) : d331593 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36300, d331593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36300, d331593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36301 q = 1) (hb : d331335 q = 1) : d331594 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36301, d331594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36301, d331594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36455 q = 1) (hb : d331335 q = 1) : d331699 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36455, d331699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90429 q ha hb
    | true =>
      simp only [d36455, d331699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36456 q = 1) (hb : d331335 q = 1) : d331700 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36456, d331700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36456, d331700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36457 q = 1) (hb : d331335 q = 1) : d331701 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36457, d331701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36457, d331701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36458 q = 1) (hb : d331335 q = 1) : d331702 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36458, d331702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36458, d331702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36459 q = 1) (hb : d331335 q = 1) : d331703 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36459, d331703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36459, d331703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36460 q = 1) (hb : d331335 q = 1) : d331704 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36460, d331704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36460, d331704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro90435 (p : Pattern) (ha : d36466 p = 1) (hb : d331335 p = 1) : d331710 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36455 q = 1) (hb : d331335 q = 1) : d331699 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36455, d331699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90429 q ha hb
    | true =>
      simp only [d36455, d331699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36456 q = 1) (hb : d331335 q = 1) : d331700 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36456, d331700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36456, d331700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36457 q = 1) (hb : d331335 q = 1) : d331701 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36457, d331701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36457, d331701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36458 q = 1) (hb : d331335 q = 1) : d331702 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36458, d331702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36458, d331702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36459 q = 1) (hb : d331335 q = 1) : d331703 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36459, d331703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36459, d331703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36461 q = 1) (hb : d331335 q = 1) : d331705 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36461, d331705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90432 q ha hb
    | true =>
      simp only [d36461, d331705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36462 q = 1) (hb : d331335 q = 1) : d331706 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36462, d331706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36462, d331706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36463 q = 1) (hb : d331335 q = 1) : d331707 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36463, d331707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36463, d331707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36464 q = 1) (hb : d331335 q = 1) : d331708 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36464, d331708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36464, d331708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36465 q = 1) (hb : d331335 q = 1) : d331709 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36465, d331709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36465, d331709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36466 q = 1) (hb : d331335 q = 1) : d331710 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36466, d331710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36466, d331710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro90436 (p : Pattern) (ha : d36475 p = 1) (hb : d331335 p = 1) : d331719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36461 q = 1) (hb : d331335 q = 1) : d331705 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36461, d331705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90432 q ha hb
    | true =>
      simp only [d36461, d331705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36462 q = 1) (hb : d331335 q = 1) : d331706 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36462, d331706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36462, d331706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36463 q = 1) (hb : d331335 q = 1) : d331707 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36463, d331707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36463, d331707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36464 q = 1) (hb : d331335 q = 1) : d331708 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36464, d331708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36464, d331708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36465 q = 1) (hb : d331335 q = 1) : d331709 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36465, d331709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36465, d331709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36475 q = 1) (hb : d331335 q = 1) : d331719 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36475, d331719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36475, d331719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90437 (p : Pattern) (ha : d36518 p = 1) (hb : d331335 p = 1) : d331762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d331335 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d36057 q = 1) (hb : d331335 q = 1) : d331392 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36057, d331392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90395 q ha hb
    | true =>
      simp only [d36057, d331392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36058 q = 1) (hb : d331335 q = 1) : d331393 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36058, d331393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36058, d331393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36059 q = 1) (hb : d331335 q = 1) : d331394 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36059, d331394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36059, d331394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36508 q = 1) (hb : d331335 q = 1) : d331752 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36508, d331752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36508, d331752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36517 q = 1) (hb : d331335 q = 1) : d331761 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36517, d331761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36517, d331761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36518 q = 1) (hb : d331335 q = 1) : d331762 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36518, d331762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36518, d331762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro90438 (p : Pattern) (ha : d36574 p = 1) (hb : d331335 p = 1) : d331785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36519 q = 1) (hb : d331335 q = 1) : d331763 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36519, d331763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90437 q ha hb
    | true =>
      simp only [d36519, d331763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36520 q = 1) (hb : d331335 q = 1) : d331764 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36520, d331764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36520, d331764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36571 q = 1) (hb : d331335 q = 1) : d331782 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36571, d331782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36571, d331782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36572 q = 1) (hb : d331335 q = 1) : d331783 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36572, d331783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36572, d331783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36573 q = 1) (hb : d331335 q = 1) : d331784 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36573, d331784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36573, d331784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36574 q = 1) (hb : d331335 q = 1) : d331785 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36574, d331785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36574, d331785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90439 (p : Pattern) (ha : d36580 p = 1) (hb : d331335 p = 1) : d331791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36575 q = 1) (hb : d331335 q = 1) : d331786 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36575, d331786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90438 q ha hb
    | true =>
      simp only [d36575, d331786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36576 q = 1) (hb : d331335 q = 1) : d331787 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36576, d331787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36576, d331787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36577 q = 1) (hb : d331335 q = 1) : d331788 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36577, d331788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36577, d331788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36578 q = 1) (hb : d331335 q = 1) : d331789 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36578, d331789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36578, d331789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36579 q = 1) (hb : d331335 q = 1) : d331790 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36579, d331790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36579, d331790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36580 q = 1) (hb : d331335 q = 1) : d331791 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36580, d331791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36580, d331791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90440 (p : Pattern) (ha : d36317 p = 1) (hb : d331335 p = 1) : d331610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36283 q = 1) (hb : d331335 q = 1) : d331576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36283, d331576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90426 q ha hb
    | true =>
      simp only [d36283, d331576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36284 q = 1) (hb : d331335 q = 1) : d331577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36284, d331577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36284, d331577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36287 q = 1) (hb : d331335 q = 1) : d331580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90427 q ha hb
    | true =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36288 q = 1) (hb : d331335 q = 1) : d331581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36289 q = 1) (hb : d331335 q = 1) : d331582 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36289, d331582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36289, d331582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36290 q = 1) (hb : d331335 q = 1) : d331583 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36290, d331583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36290, d331583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36316 q = 1) (hb : d331335 q = 1) : d331609 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36316, d331609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36316, d331609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36317 q = 1) (hb : d331335 q = 1) : d331610 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36317, d331610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36317, d331610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90441 (p : Pattern) (ha : d36319 p = 1) (hb : d331335 p = 1) : d331612 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36287 q = 1) (hb : d331335 q = 1) : d331580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90427 q ha hb
    | true =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36288 q = 1) (hb : d331335 q = 1) : d331581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36293 q = 1) (hb : d331335 q = 1) : d331586 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36293, d331586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36293, d331586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36294 q = 1) (hb : d331335 q = 1) : d331587 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36294, d331587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36294, d331587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36318 q = 1) (hb : d331335 q = 1) : d331611 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36318, d331611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36318, d331611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36319 q = 1) (hb : d331335 q = 1) : d331612 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36319, d331612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36319, d331612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90442 (p : Pattern) (ha : d36326 p = 1) (hb : d331335 p = 1) : d331619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36283 q = 1) (hb : d331335 q = 1) : d331576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36283, d331576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90426 q ha hb
    | true =>
      simp only [d36283, d331576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36284 q = 1) (hb : d331335 q = 1) : d331577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36284, d331577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36284, d331577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36287 q = 1) (hb : d331335 q = 1) : d331580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90427 q ha hb
    | true =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36288 q = 1) (hb : d331335 q = 1) : d331581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36289 q = 1) (hb : d331335 q = 1) : d331582 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36289, d331582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36289, d331582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36324 q = 1) (hb : d331335 q = 1) : d331617 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36324, d331617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36324, d331617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36325 q = 1) (hb : d331335 q = 1) : d331618 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36325, d331618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36325, d331618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36326 q = 1) (hb : d331335 q = 1) : d331619 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36326, d331619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36326, d331619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90443 (p : Pattern) (ha : d36329 p = 1) (hb : d331335 p = 1) : d331622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36287 q = 1) (hb : d331335 q = 1) : d331580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90427 q ha hb
    | true =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36288 q = 1) (hb : d331335 q = 1) : d331581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36293 q = 1) (hb : d331335 q = 1) : d331586 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36293, d331586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36293, d331586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36327 q = 1) (hb : d331335 q = 1) : d331620 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36327, d331620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36327, d331620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36328 q = 1) (hb : d331335 q = 1) : d331621 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36328, d331621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36328, d331621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36329 q = 1) (hb : d331335 q = 1) : d331622 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36329, d331622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36329, d331622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90444 (p : Pattern) (ha : d36334 p = 1) (hb : d331335 p = 1) : d43406 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331334 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d307 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d14, d307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d309 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d825 q = 1) (hb : d253504 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d825, d253504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d825, d253504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h10 (q : Pattern) (ha : d36333 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d36333, d331335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36333, d331335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d271213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307, d271213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d271213 q = 1) : d308 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309 q = 1) (hb : d271213 q = 1) : d1523 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, d1523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309, d1523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d825 q = 1) (hb : d331334 q = 1) : d2005 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d825, d331334, d2005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d825, d331334, d2005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h15 (q : Pattern) (ha : d14 q = 1) (hb : d128 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14, d128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d14 q = 1) (hb : d14 q = 1) : d14 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d14 q = 1) (hb : d129 q = 1) : d1084 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129, d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d534 q = 1) (hb : d253504 q = 1) : d1085 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d534, d253504, d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
    | true =>
      simp only [d534, d253504, d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h19 (q : Pattern) (ha : d36113 q = 1) (hb : d331335 q = 1) : d42940 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d36113, d331335, d42940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d36113, d331335, d42940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d36334 q = 1) (hb : d331335 q = 1) : d43406 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d36334, d43406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36334, d43406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro90445 (p : Pattern) (ha : d36340 p = 1) (hb : d331335 p = 1) : d331629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36335 q = 1) (hb : d331335 q = 1) : d43407 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d36335, d43407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90444 q ha hb
    | true =>
      simp only [d36335, d43407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36336 q = 1) (hb : d331335 q = 1) : d43408 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d36336, d43408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36336, d43408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36115 q = 1) (hb : d331335 q = 1) : d331449 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d36115, d331449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90405 q ha hb
    | true =>
      simp only [d36115, d331449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36116 q = 1) (hb : d331335 q = 1) : d331450 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d36116, d331450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36116, d331450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36337 q = 1) (hb : d331335 q = 1) : d331626 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d36337, d331626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36337, d331626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9452 q = 1) (hb : d331335 q = 1) : d331337 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d331337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90386 q ha hb
    | true =>
      simp only [d9452, d331337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9453 q = 1) (hb : d331335 q = 1) : d331338 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d331338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9453, d331338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36117 q = 1) (hb : d331335 q = 1) : d331451 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d36117, d331451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36117, d331451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36338 q = 1) (hb : d331335 q = 1) : d331627 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36338, d331627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36338, d331627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36339 q = 1) (hb : d331335 q = 1) : d331628 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36339, d331628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36339, d331628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20 q = 1) (hb : d331335 q = 1) : d20 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d9454 q = 1) (hb : d331335 q = 1) : d331339 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9454, d331339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9454, d331339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d36118 q = 1) (hb : d331335 q = 1) : d331452 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36118, d331452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36118, d331452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d36119 q = 1) (hb : d331335 q = 1) : d331453 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36119, d331453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36119, d331453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d36340 q = 1) (hb : d331335 q = 1) : d331629 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d36340, d331629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36340, d331629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro90446 (p : Pattern) (ha : d36345 p = 1) (hb : d331335 p = 1) : d331634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36115 q = 1) (hb : d331335 q = 1) : d331449 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d36115, d331449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90405 q ha hb
    | true =>
      simp only [d36115, d331449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36116 q = 1) (hb : d331335 q = 1) : d331450 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d36116, d331450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36116, d331450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9452 q = 1) (hb : d331335 q = 1) : d331337 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d331337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90386 q ha hb
    | true =>
      simp only [d9452, d331337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9453 q = 1) (hb : d331335 q = 1) : d331338 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d331338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9453, d331338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36117 q = 1) (hb : d331335 q = 1) : d331451 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d36117, d331451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36117, d331451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20 q = 1) (hb : d331335 q = 1) : d20 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9454 q = 1) (hb : d331335 q = 1) : d331339 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9454, d331339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9454, d331339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36118 q = 1) (hb : d331335 q = 1) : d331452 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36118, d331452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36118, d331452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36119 q = 1) (hb : d331335 q = 1) : d331453 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36119, d331453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36119, d331453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9455 q = 1) (hb : d331335 q = 1) : d331460 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9455, d331460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9455, d331460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9456 q = 1) (hb : d331335 q = 1) : d331461 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9456, d331461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9456, d331461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d36345 q = 1) (hb : d331335 q = 1) : d331634 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d36345, d331634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36345, d331634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro90447 (p : Pattern) (ha : d36353 p = 1) (hb : d331335 p = 1) : d331642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36115 q = 1) (hb : d331335 q = 1) : d331449 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d36115, d331449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90405 q ha hb
    | true =>
      simp only [d36115, d331449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36116 q = 1) (hb : d331335 q = 1) : d331450 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d36116, d331450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36116, d331450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9452 q = 1) (hb : d331335 q = 1) : d331337 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d331337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90386 q ha hb
    | true =>
      simp only [d9452, d331337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9453 q = 1) (hb : d331335 q = 1) : d331338 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d331338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9453, d331338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36117 q = 1) (hb : d331335 q = 1) : d331451 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d36117, d331451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36117, d331451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36351 q = 1) (hb : d331335 q = 1) : d331640 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36351, d331640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36351, d331640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36352 q = 1) (hb : d331335 q = 1) : d331641 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36352, d331641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36352, d331641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20 q = 1) (hb : d331335 q = 1) : d20 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9454 q = 1) (hb : d331335 q = 1) : d331339 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9454, d331339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9454, d331339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9455 q = 1) (hb : d331335 q = 1) : d331460 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9455, d331460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9455, d331460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9456 q = 1) (hb : d331335 q = 1) : d331461 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9456, d331461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9456, d331461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d36353 q = 1) (hb : d331335 q = 1) : d331642 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d36353, d331642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36353, d331642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro90448 (p : Pattern) (ha : d36359 p = 1) (hb : d331335 p = 1) : d331648 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36341 q = 1) (hb : d331335 q = 1) : d331630 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36341, d331630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90445 q ha hb
    | true =>
      simp only [d36341, d331630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36342 q = 1) (hb : d331335 q = 1) : d331631 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36342, d331631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36342, d331631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36343 q = 1) (hb : d331335 q = 1) : d331632 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36343, d331632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36343, d331632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36344 q = 1) (hb : d331335 q = 1) : d331633 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36344, d331633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36344, d331633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36346 q = 1) (hb : d331335 q = 1) : d331635 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36346, d331635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90446 q ha hb
    | true =>
      simp only [d36346, d331635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36347 q = 1) (hb : d331335 q = 1) : d331636 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36347, d331636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36347, d331636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36348 q = 1) (hb : d331335 q = 1) : d331637 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36348, d331637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36348, d331637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36349 q = 1) (hb : d331335 q = 1) : d331638 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36349, d331638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36349, d331638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36350 q = 1) (hb : d331335 q = 1) : d331639 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36350, d331639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36350, d331639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36354 q = 1) (hb : d331335 q = 1) : d331643 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36354, d331643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90447 q ha hb
    | true =>
      simp only [d36354, d331643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36355 q = 1) (hb : d331335 q = 1) : d331644 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36355, d331644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36355, d331644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d36356 q = 1) (hb : d331335 q = 1) : d331645 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36356, d331645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36356, d331645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d36357 q = 1) (hb : d331335 q = 1) : d331646 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36357, d331646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d36357, d331646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d36127 q = 1) (hb : d331335 q = 1) : d331463 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36127, d331463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90407 q ha hb
    | true =>
      simp only [d36127, d331463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d36128 q = 1) (hb : d331335 q = 1) : d331464 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36128, d331464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d36128, d331464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d36129 q = 1) (hb : d331335 q = 1) : d331465 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36129, d331465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36129, d331465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36130 q = 1) (hb : d331335 q = 1) : d331466 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36130, d331466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d36130, d331466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d36358 q = 1) (hb : d331335 q = 1) : d331647 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36358, d331647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36358, d331647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d36359 q = 1) (hb : d331335 q = 1) : d331648 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36359, d331648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36359, d331648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro90449 (p : Pattern) (ha : d36363 p = 1) (hb : d331335 p = 1) : d331652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36127 q = 1) (hb : d331335 q = 1) : d331463 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36127, d331463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90407 q ha hb
    | true =>
      simp only [d36127, d331463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36128 q = 1) (hb : d331335 q = 1) : d331464 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36128, d331464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36128, d331464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36129 q = 1) (hb : d331335 q = 1) : d331465 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36129, d331465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36129, d331465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36130 q = 1) (hb : d331335 q = 1) : d331466 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36130, d331466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36130, d331466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d331335 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d36131 q = 1) (hb : d331335 q = 1) : d331467 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36131, d331467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36131, d331467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d331335 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d36363 q = 1) (hb : d331335 q = 1) : d331652 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36363, d331652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36363, d331652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90450 (p : Pattern) (ha : d36369 p = 1) (hb : d331335 p = 1) : d331658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36360 q = 1) (hb : d331335 q = 1) : d331649 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36360, d331649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90448 q ha hb
    | true =>
      simp only [d36360, d331649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90408 q ha hb
  have h2 (q : Pattern) (ha : d36361 q = 1) (hb : d331335 q = 1) : d331650 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36361, d331650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36361, d331650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36362 q = 1) (hb : d331335 q = 1) : d331651 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36362, d331651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36362, d331651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36364 q = 1) (hb : d331335 q = 1) : d331653 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36364, d331653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90408 q ha hb
    | true =>
      simp only [d36364, d331653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90449 q ha hb
  have h5 (q : Pattern) (ha : d36365 q = 1) (hb : d331335 q = 1) : d331654 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36365, d331654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36365, d331654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36366 q = 1) (hb : d331335 q = 1) : d331655 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36366, d331655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36366, d331655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36367 q = 1) (hb : d331335 q = 1) : d331656 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36367, d331656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36367, d331656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36133 q = 1) (hb : d331335 q = 1) : d331469 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36133, d331469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90408 q ha hb
    | true =>
      simp only [d36133, d331469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90388 q ha hb
  have h9 (q : Pattern) (ha : d36134 q = 1) (hb : d331335 q = 1) : d331470 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36134, d331470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36134, d331470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36135 q = 1) (hb : d331335 q = 1) : d331471 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36135, d331471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36135, d331471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d331335 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d36014 q = 1) (hb : d331335 q = 1) : d331349 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36014, d331349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90388 q ha hb
    | true =>
      simp only [d36014, d331349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d36015 q = 1) (hb : d331335 q = 1) : d331350 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36015, d331350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36015, d331350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d36016 q = 1) (hb : d331335 q = 1) : d331351 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36016, d331351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36016, d331351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d36136 q = 1) (hb : d331335 q = 1) : d331472 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36136, d331472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36136, d331472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d36368 q = 1) (hb : d331335 q = 1) : d331657 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36368, d331657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36368, d331657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36369 q = 1) (hb : d331335 q = 1) : d331658 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36369, d331658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d36369, d331658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro90451 (p : Pattern) (ha : d36375 p = 1) (hb : d331335 p = 1) : d331664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36370 q = 1) (hb : d331335 q = 1) : d331659 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36370, d331659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90450 q ha hb
    | true =>
      simp only [d36370, d331659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36371 q = 1) (hb : d331335 q = 1) : d331660 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36371, d331660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36371, d331660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36283 q = 1) (hb : d331335 q = 1) : d331576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36283, d331576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90426 q ha hb
    | true =>
      simp only [d36283, d331576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36284 q = 1) (hb : d331335 q = 1) : d331577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36284, d331577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36284, d331577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36372 q = 1) (hb : d331335 q = 1) : d331661 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36372, d331661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36372, d331661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36373 q = 1) (hb : d331335 q = 1) : d331662 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36373, d331662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36373, d331662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36374 q = 1) (hb : d331335 q = 1) : d331663 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36374, d331663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36374, d331663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36375 q = 1) (hb : d331335 q = 1) : d331664 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36375, d331664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36375, d331664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90452 (p : Pattern) (ha : d36423 p = 1) (hb : d331335 p = 1) : d331670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36283 q = 1) (hb : d331335 q = 1) : d331576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36283, d331576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90426 q ha hb
    | true =>
      simp only [d36283, d331576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36284 q = 1) (hb : d331335 q = 1) : d331577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36284, d331577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36284, d331577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36420 q = 1) (hb : d331335 q = 1) : d331667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36420, d331667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36420, d331667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36421 q = 1) (hb : d331335 q = 1) : d331668 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36421, d331668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36421, d331668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36422 q = 1) (hb : d331335 q = 1) : d331669 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36422, d331669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36422, d331669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36423 q = 1) (hb : d331335 q = 1) : d331670 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36423, d331670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36423, d331670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90453 (p : Pattern) (ha : d269992 p = 1) (hb : d331335 p = 1) : d331676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36320 q = 1) (hb : d331335 q = 1) : d331613 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36320, d331613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90440 q ha hb
    | true =>
      simp only [d36320, d331613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90441 q ha hb
  have h2 (q : Pattern) (ha : d36321 q = 1) (hb : d331335 q = 1) : d331614 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36321, d331614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36321, d331614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36322 q = 1) (hb : d331335 q = 1) : d331615 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36322, d331615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36322, d331615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36323 q = 1) (hb : d331335 q = 1) : d331616 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36323, d331616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36323, d331616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36330 q = 1) (hb : d331335 q = 1) : d331623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36330, d331623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90442 q ha hb
    | true =>
      simp only [d36330, d331623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90443 q ha hb
  have h6 (q : Pattern) (ha : d36331 q = 1) (hb : d331335 q = 1) : d331624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36331, d331624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36331, d331624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36332 q = 1) (hb : d331335 q = 1) : d331625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36332, d331625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36332, d331625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36376 q = 1) (hb : d331335 q = 1) : d331665 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36376, d331665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90451 q ha hb
    | true =>
      simp only [d36376, d331665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90428 q ha hb
  have h9 (q : Pattern) (ha : d269988 q = 1) (hb : d331335 q = 1) : d331666 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269988, d331666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269988, d331666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d36424 q = 1) (hb : d331335 q = 1) : d331671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36424, d331671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90452 q ha hb
    | true =>
      simp only [d36424, d331671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36425 q = 1) (hb : d331335 q = 1) : d331672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36425, d331672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36425, d331672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d269989 q = 1) (hb : d331335 q = 1) : d331673 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269989, d331673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269989, d331673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269990 q = 1) (hb : d331335 q = 1) : d331674 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269990, d331674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269990, d331674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269991 q = 1) (hb : d331335 q = 1) : d331675 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269991, d331675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269991, d331675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d269992 q = 1) (hb : d331335 q = 1) : d331676 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269992, d331676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d269992, d331676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro90454 (p : Pattern) (ha : d36430 p = 1) (hb : d331335 p = 1) : d331677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36283 q = 1) (hb : d331335 q = 1) : d331576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36283, d331576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90426 q ha hb
    | true =>
      simp only [d36283, d331576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36284 q = 1) (hb : d331335 q = 1) : d331577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36284, d331577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36284, d331577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36287 q = 1) (hb : d331335 q = 1) : d331580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90427 q ha hb
    | true =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36288 q = 1) (hb : d331335 q = 1) : d331581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36289 q = 1) (hb : d331335 q = 1) : d331582 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36289, d331582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36289, d331582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36290 q = 1) (hb : d331335 q = 1) : d331583 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36290, d331583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36290, d331583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36316 q = 1) (hb : d331335 q = 1) : d331609 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36316, d331609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36316, d331609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36430 q = 1) (hb : d331335 q = 1) : d331677 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36430, d331677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36430, d331677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro90455 (p : Pattern) (ha : d36431 p = 1) (hb : d331335 p = 1) : d331678 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36287 q = 1) (hb : d331335 q = 1) : d331580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90427 q ha hb
    | true =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36288 q = 1) (hb : d331335 q = 1) : d331581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36293 q = 1) (hb : d331335 q = 1) : d331586 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36293, d331586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36293, d331586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36294 q = 1) (hb : d331335 q = 1) : d331587 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36294, d331587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36294, d331587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36318 q = 1) (hb : d331335 q = 1) : d331611 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36318, d331611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36318, d331611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36431 q = 1) (hb : d331335 q = 1) : d331678 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36431, d331678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36431, d331678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90456 (p : Pattern) (ha : d36436 p = 1) (hb : d331335 p = 1) : d331683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36283 q = 1) (hb : d331335 q = 1) : d331576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36283, d331576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90426 q ha hb
    | true =>
      simp only [d36283, d331576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36284 q = 1) (hb : d331335 q = 1) : d331577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36284, d331577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36284, d331577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36287 q = 1) (hb : d331335 q = 1) : d331580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90427 q ha hb
    | true =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36288 q = 1) (hb : d331335 q = 1) : d331581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36289 q = 1) (hb : d331335 q = 1) : d331582 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36289, d331582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36289, d331582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36324 q = 1) (hb : d331335 q = 1) : d331617 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36324, d331617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36324, d331617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36325 q = 1) (hb : d331335 q = 1) : d331618 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36325, d331618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36325, d331618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36436 q = 1) (hb : d331335 q = 1) : d331683 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36436, d331683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36436, d331683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro90457 (p : Pattern) (ha : d36437 p = 1) (hb : d331335 p = 1) : d331684 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36287 q = 1) (hb : d331335 q = 1) : d331580 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90427 q ha hb
    | true =>
      simp only [d36287, d331580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36288 q = 1) (hb : d331335 q = 1) : d331581 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36288, d331581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36293 q = 1) (hb : d331335 q = 1) : d331586 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36293, d331586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36293, d331586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36327 q = 1) (hb : d331335 q = 1) : d331620 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36327, d331620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36327, d331620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36328 q = 1) (hb : d331335 q = 1) : d331621 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36328, d331621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36328, d331621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36437 q = 1) (hb : d331335 q = 1) : d331684 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36437, d331684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36437, d331684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90458 (p : Pattern) (ha : d36441 p = 1) (hb : d331335 p = 1) : d331688 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36370 q = 1) (hb : d331335 q = 1) : d331659 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36370, d331659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90450 q ha hb
    | true =>
      simp only [d36370, d331659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36371 q = 1) (hb : d331335 q = 1) : d331660 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36371, d331660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36371, d331660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36283 q = 1) (hb : d331335 q = 1) : d331576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36283, d331576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90426 q ha hb
    | true =>
      simp only [d36283, d331576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36284 q = 1) (hb : d331335 q = 1) : d331577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36284, d331577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36284, d331577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36372 q = 1) (hb : d331335 q = 1) : d331661 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36372, d331661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36372, d331661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36373 q = 1) (hb : d331335 q = 1) : d331662 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36373, d331662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36373, d331662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36374 q = 1) (hb : d331335 q = 1) : d331663 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36374, d331663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36374, d331663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36441 q = 1) (hb : d331335 q = 1) : d331688 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36441, d331688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36441, d331688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro90459 (p : Pattern) (ha : d36447 p = 1) (hb : d331335 p = 1) : d331691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36283 q = 1) (hb : d331335 q = 1) : d331576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36283, d331576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90426 q ha hb
    | true =>
      simp only [d36283, d331576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36284 q = 1) (hb : d331335 q = 1) : d331577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36284, d331577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36284, d331577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36420 q = 1) (hb : d331335 q = 1) : d331667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36420, d331667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36420, d331667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36421 q = 1) (hb : d331335 q = 1) : d331668 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36421, d331668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36421, d331668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36422 q = 1) (hb : d331335 q = 1) : d331669 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36422, d331669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36422, d331669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36447 q = 1) (hb : d331335 q = 1) : d331691 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36447, d331691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36447, d331691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90460 (p : Pattern) (ha : d269997 p = 1) (hb : d331335 p = 1) : d331697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36320 q = 1) (hb : d331335 q = 1) : d331613 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36320, d331613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90440 q ha hb
    | true =>
      simp only [d36320, d331613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90441 q ha hb
  have h2 (q : Pattern) (ha : d36321 q = 1) (hb : d331335 q = 1) : d331614 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36321, d331614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36321, d331614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36322 q = 1) (hb : d331335 q = 1) : d331615 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36322, d331615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36322, d331615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36323 q = 1) (hb : d331335 q = 1) : d331616 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36323, d331616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36323, d331616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36330 q = 1) (hb : d331335 q = 1) : d331623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36330, d331623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90442 q ha hb
    | true =>
      simp only [d36330, d331623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90443 q ha hb
  have h6 (q : Pattern) (ha : d36331 q = 1) (hb : d331335 q = 1) : d331624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36331, d331624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36331, d331624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36332 q = 1) (hb : d331335 q = 1) : d331625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36332, d331625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36332, d331625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36376 q = 1) (hb : d331335 q = 1) : d331665 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36376, d331665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90451 q ha hb
    | true =>
      simp only [d36376, d331665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90428 q ha hb
  have h9 (q : Pattern) (ha : d269988 q = 1) (hb : d331335 q = 1) : d331666 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269988, d331666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d269988, d331666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d36424 q = 1) (hb : d331335 q = 1) : d331671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36424, d331671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90452 q ha hb
    | true =>
      simp only [d36424, d331671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36425 q = 1) (hb : d331335 q = 1) : d331672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36425, d331672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36425, d331672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d269989 q = 1) (hb : d331335 q = 1) : d331673 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269989, d331673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d269989, d331673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d269990 q = 1) (hb : d331335 q = 1) : d331674 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269990, d331674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d269990, d331674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d269991 q = 1) (hb : d331335 q = 1) : d331675 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269991, d331675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d269991, d331675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d36432 q = 1) (hb : d331335 q = 1) : d331679 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36432, d331679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90454 q ha hb
    | true =>
      simp only [d36432, d331679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90455 q ha hb
  have h16 (q : Pattern) (ha : d36433 q = 1) (hb : d331335 q = 1) : d331680 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36433, d331680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36433, d331680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36434 q = 1) (hb : d331335 q = 1) : d331681 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36434, d331681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d36434, d331681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d36435 q = 1) (hb : d331335 q = 1) : d331682 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36435, d331682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36435, d331682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d36438 q = 1) (hb : d331335 q = 1) : d331685 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36438, d331685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90456 q ha hb
    | true =>
      simp only [d36438, d331685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90457 q ha hb
  have h20 (q : Pattern) (ha : d36439 q = 1) (hb : d331335 q = 1) : d331686 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36439, d331686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36439, d331686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d36440 q = 1) (hb : d331335 q = 1) : d331687 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36440, d331687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d36440, d331687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d36442 q = 1) (hb : d331335 q = 1) : d331689 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36442, d331689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90458 q ha hb
    | true =>
      simp only [d36442, d331689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90431 q ha hb
  have h23 (q : Pattern) (ha : d269993 q = 1) (hb : d331335 q = 1) : d331690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269993, d331690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d269993, d331690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d36448 q = 1) (hb : d331335 q = 1) : d331692 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36448, d331692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90459 q ha hb
    | true =>
      simp only [d36448, d331692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d36449 q = 1) (hb : d331335 q = 1) : d331693 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36449, d331693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d36449, d331693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d269994 q = 1) (hb : d331335 q = 1) : d331694 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269994, d331694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d269994, d331694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d269995 q = 1) (hb : d331335 q = 1) : d331695 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d269995, d331695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d269995, d331695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d269996 q = 1) (hb : d331335 q = 1) : d331696 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d269996, d331696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d269996, d331696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d269997 q = 1) (hb : d331335 q = 1) : d331697 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d269997, d331697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d269997, d331697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro90461 (p : Pattern) (ha : d270004 p = 1) (hb : d331335 p = 1) : d331717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36442 q = 1) (hb : d331335 q = 1) : d331689 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36442, d331689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90458 q ha hb
    | true =>
      simp only [d36442, d331689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90431 q ha hb
  have h2 (q : Pattern) (ha : d269993 q = 1) (hb : d331335 q = 1) : d331690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d269993, d331690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d269993, d331690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36448 q = 1) (hb : d331335 q = 1) : d331692 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36448, d331692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90459 q ha hb
    | true =>
      simp only [d36448, d331692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36449 q = 1) (hb : d331335 q = 1) : d331693 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36449, d331693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36449, d331693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d269994 q = 1) (hb : d331335 q = 1) : d331694 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d269994, d331694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d269994, d331694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270002 q = 1) (hb : d331335 q = 1) : d331715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270002, d331715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270002, d331715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270003 q = 1) (hb : d331335 q = 1) : d331716 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270003, d331716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270003, d331716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270004 q = 1) (hb : d331335 q = 1) : d331717 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270004, d331717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270004, d331717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90462 (p : Pattern) (ha : d36495 p = 1) (hb : d331335 p = 1) : d331739 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36481 q = 1) (hb : d331335 q = 1) : d331725 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36481, d331725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36481, d331725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90445 q ha hb
  have h2 (q : Pattern) (ha : d36341 q = 1) (hb : d331335 q = 1) : d331630 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36341, d331630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90445 q ha hb
    | true =>
      simp only [d36341, d331630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36482 q = 1) (hb : d331335 q = 1) : d331726 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36482, d331726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36482, d331726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36342 q = 1) (hb : d331335 q = 1) : d331631 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36342, d331631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36342, d331631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36483 q = 1) (hb : d331335 q = 1) : d331727 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36483, d331727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36483, d331727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36484 q = 1) (hb : d331335 q = 1) : d331728 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36484, d331728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36484, d331728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36485 q = 1) (hb : d331335 q = 1) : d331729 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36485, d331729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36485, d331729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90446 q ha hb
  have h8 (q : Pattern) (ha : d36346 q = 1) (hb : d331335 q = 1) : d331635 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36346, d331635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90446 q ha hb
    | true =>
      simp only [d36346, d331635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36486 q = 1) (hb : d331335 q = 1) : d331730 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36486, d331730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36486, d331730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36347 q = 1) (hb : d331335 q = 1) : d331636 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36347, d331636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36347, d331636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36487 q = 1) (hb : d331335 q = 1) : d331731 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36487, d331731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36487, d331731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d36488 q = 1) (hb : d331335 q = 1) : d331732 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36488, d331732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36488, d331732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d36489 q = 1) (hb : d331335 q = 1) : d331733 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36489, d331733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36489, d331733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d36490 q = 1) (hb : d331335 q = 1) : d331734 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36490, d331734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36490, d331734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90447 q ha hb
  have h15 (q : Pattern) (ha : d36354 q = 1) (hb : d331335 q = 1) : d331643 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36354, d331643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90447 q ha hb
    | true =>
      simp only [d36354, d331643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d36491 q = 1) (hb : d331335 q = 1) : d331735 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36491, d331735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d36491, d331735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36355 q = 1) (hb : d331335 q = 1) : d331644 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36355, d331644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d36355, d331644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d36492 q = 1) (hb : d331335 q = 1) : d331736 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36492, d331736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d36492, d331736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d36493 q = 1) (hb : d331335 q = 1) : d331737 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36493, d331737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d36493, d331737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d36219 q = 1) (hb : d331335 q = 1) : d331531 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36219, d331531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36219, d331531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90407 q ha hb
  have h21 (q : Pattern) (ha : d36127 q = 1) (hb : d331335 q = 1) : d331463 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36127, d331463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90407 q ha hb
    | true =>
      simp only [d36127, d331463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d36220 q = 1) (hb : d331335 q = 1) : d331532 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36220, d331532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d36220, d331532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d36128 q = 1) (hb : d331335 q = 1) : d331464 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36128, d331464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d36128, d331464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d36221 q = 1) (hb : d331335 q = 1) : d331533 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36221, d331533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d36221, d331533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d36222 q = 1) (hb : d331335 q = 1) : d331534 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36222, d331534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d36222, d331534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d36494 q = 1) (hb : d331335 q = 1) : d331738 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36494, d331738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d36494, d331738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d36495 q = 1) (hb : d331335 q = 1) : d331739 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36495, d331739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36495, d331739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro90463 (p : Pattern) (ha : d36499 p = 1) (hb : d331335 p = 1) : d331743 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36219 q = 1) (hb : d331335 q = 1) : d331531 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36219, d331531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36219, d331531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90407 q ha hb
  have h2 (q : Pattern) (ha : d36127 q = 1) (hb : d331335 q = 1) : d331463 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36127, d331463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90407 q ha hb
    | true =>
      simp only [d36127, d331463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36220 q = 1) (hb : d331335 q = 1) : d331532 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36220, d331532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36220, d331532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36128 q = 1) (hb : d331335 q = 1) : d331464 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36128, d331464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36128, d331464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36221 q = 1) (hb : d331335 q = 1) : d331533 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36221, d331533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36221, d331533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36222 q = 1) (hb : d331335 q = 1) : d331534 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36222, d331534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36222, d331534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d331335 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d36223 q = 1) (hb : d331335 q = 1) : d331535 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36223, d331535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36223, d331535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d331335 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d36499 q = 1) (hb : d331335 q = 1) : d331743 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36499, d331743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36499, d331743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro90464 (p : Pattern) (ha : d36505 p = 1) (hb : d331335 p = 1) : d331749 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36496 q = 1) (hb : d331335 q = 1) : d331740 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36496, d331740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90462 q ha hb
    | true =>
      simp only [d36496, d331740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90419 q ha hb
  have h2 (q : Pattern) (ha : d36497 q = 1) (hb : d331335 q = 1) : d331741 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36497, d331741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36497, d331741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36498 q = 1) (hb : d331335 q = 1) : d331742 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36498, d331742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36498, d331742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36500 q = 1) (hb : d331335 q = 1) : d331744 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36500, d331744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90419 q ha hb
    | true =>
      simp only [d36500, d331744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90463 q ha hb
  have h5 (q : Pattern) (ha : d36501 q = 1) (hb : d331335 q = 1) : d331745 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36501, d331745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36501, d331745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36502 q = 1) (hb : d331335 q = 1) : d331746 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36502, d331746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36502, d331746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36503 q = 1) (hb : d331335 q = 1) : d331747 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36503, d331747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36503, d331747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36225 q = 1) (hb : d331335 q = 1) : d331537 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36225, d331537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90419 q ha hb
    | true =>
      simp only [d36225, d331537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90395 q ha hb
  have h9 (q : Pattern) (ha : d36226 q = 1) (hb : d331335 q = 1) : d331538 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36226, d331538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36226, d331538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36227 q = 1) (hb : d331335 q = 1) : d331539 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36227, d331539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36227, d331539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d331335 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d36057 q = 1) (hb : d331335 q = 1) : d331392 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36057, d331392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90395 q ha hb
    | true =>
      simp only [d36057, d331392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d36058 q = 1) (hb : d331335 q = 1) : d331393 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36058, d331393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36058, d331393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d36059 q = 1) (hb : d331335 q = 1) : d331394 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36059, d331394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36059, d331394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d36228 q = 1) (hb : d331335 q = 1) : d331540 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36228, d331540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36228, d331540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d36504 q = 1) (hb : d331335 q = 1) : d331748 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36504, d331748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36504, d331748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36505 q = 1) (hb : d331335 q = 1) : d331749 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36505, d331749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d36505, d331749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro90465 (p : Pattern) (ha : d36510 p = 1) (hb : d331335 p = 1) : d331754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36225 q = 1) (hb : d331335 q = 1) : d331537 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36225, d331537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90419 q ha hb
    | true =>
      simp only [d36225, d331537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90395 q ha hb
  have h2 (q : Pattern) (ha : d36226 q = 1) (hb : d331335 q = 1) : d331538 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36226, d331538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36226, d331538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36227 q = 1) (hb : d331335 q = 1) : d331539 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36227, d331539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36227, d331539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d331335 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d36057 q = 1) (hb : d331335 q = 1) : d331392 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36057, d331392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90395 q ha hb
    | true =>
      simp only [d36057, d331392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36058 q = 1) (hb : d331335 q = 1) : d331393 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36058, d331393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36058, d331393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36059 q = 1) (hb : d331335 q = 1) : d331394 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36059, d331394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36059, d331394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36228 q = 1) (hb : d331335 q = 1) : d331540 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36228, d331540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36228, d331540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36508 q = 1) (hb : d331335 q = 1) : d331752 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36508, d331752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36508, d331752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d36509 q = 1) (hb : d331335 q = 1) : d331753 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36509, d331753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36509, d331753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36510 q = 1) (hb : d331335 q = 1) : d331754 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36510, d331754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36510, d331754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro90466 (p : Pattern) (ha : d36516 p = 1) (hb : d331335 p = 1) : d331760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36506 q = 1) (hb : d331335 q = 1) : d331750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36506, d331750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90464 q ha hb
    | true =>
      simp only [d36506, d331750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36507 q = 1) (hb : d331335 q = 1) : d331751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36507, d331751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36507, d331751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36511 q = 1) (hb : d331335 q = 1) : d331755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36511, d331755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90465 q ha hb
    | true =>
      simp only [d36511, d331755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36512 q = 1) (hb : d331335 q = 1) : d331756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36512, d331756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36512, d331756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36513 q = 1) (hb : d331335 q = 1) : d331757 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36513, d331757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36513, d331757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36514 q = 1) (hb : d331335 q = 1) : d331758 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36514, d331758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36514, d331758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36515 q = 1) (hb : d331335 q = 1) : d331759 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36515, d331759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36515, d331759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36516 q = 1) (hb : d331335 q = 1) : d331760 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36516, d331760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36516, d331760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro90467 (p : Pattern) (ha : d36524 p = 1) (hb : d331335 p = 1) : d331768 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36511 q = 1) (hb : d331335 q = 1) : d331755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36511, d331755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90465 q ha hb
    | true =>
      simp only [d36511, d331755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36512 q = 1) (hb : d331335 q = 1) : d331756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36512, d331756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36512, d331756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36519 q = 1) (hb : d331335 q = 1) : d331763 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36519, d331763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90437 q ha hb
    | true =>
      simp only [d36519, d331763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36520 q = 1) (hb : d331335 q = 1) : d331764 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36520, d331764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36520, d331764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36521 q = 1) (hb : d331335 q = 1) : d331765 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36521, d331765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36521, d331765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36522 q = 1) (hb : d331335 q = 1) : d331766 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36522, d331766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36522, d331766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36523 q = 1) (hb : d331335 q = 1) : d331767 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36523, d331767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36523, d331767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36524 q = 1) (hb : d331335 q = 1) : d331768 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36524, d331768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36524, d331768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro90468 (p : Pattern) (ha : d36563 p = 1) (hb : d331335 p = 1) : d331774 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36511 q = 1) (hb : d331335 q = 1) : d331755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36511, d331755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90465 q ha hb
    | true =>
      simp only [d36511, d331755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36512 q = 1) (hb : d331335 q = 1) : d331756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36512, d331756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36512, d331756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36560 q = 1) (hb : d331335 q = 1) : d331771 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36560, d331771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36560, d331771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36561 q = 1) (hb : d331335 q = 1) : d331772 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36561, d331772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36561, d331772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36562 q = 1) (hb : d331335 q = 1) : d331773 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36562, d331773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36562, d331773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36563 q = 1) (hb : d331335 q = 1) : d331774 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36563, d331774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36563, d331774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90469 (p : Pattern) (ha : d270014 p = 1) (hb : d331335 p = 1) : d331780 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36525 q = 1) (hb : d331335 q = 1) : d331769 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36525, d331769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90466 q ha hb
    | true =>
      simp only [d36525, d331769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90467 q ha hb
  have h2 (q : Pattern) (ha : d270010 q = 1) (hb : d331335 q = 1) : d331770 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d270010, d331770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d270010, d331770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36564 q = 1) (hb : d331335 q = 1) : d331775 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36564, d331775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90468 q ha hb
    | true =>
      simp only [d36564, d331775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36565 q = 1) (hb : d331335 q = 1) : d331776 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36565, d331776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36565, d331776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d270011 q = 1) (hb : d331335 q = 1) : d331777 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d270011, d331777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d270011, d331777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270012 q = 1) (hb : d331335 q = 1) : d331778 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d270012, d331778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270012, d331778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d270013 q = 1) (hb : d331335 q = 1) : d331779 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d270013, d331779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270013, d331779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d270014 q = 1) (hb : d331335 q = 1) : d331780 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d270014, d331780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270014, d331780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90470 (p : Pattern) (ha : d270020 p = 1) (hb : d331335 p = 1) : d331797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36303 q = 1) (hb : d331335 q = 1) : d331596 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36303, d331596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36303, d331596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90430 q ha hb
  have h2 (q : Pattern) (ha : d36304 q = 1) (hb : d331335 q = 1) : d331597 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36304, d331597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36304, d331597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36313 q = 1) (hb : d331335 q = 1) : d331606 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36313, d331606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90430 q ha hb
    | true =>
      simp only [d36313, d331606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90433 q ha hb
  have h4 (q : Pattern) (ha : d36314 q = 1) (hb : d331335 q = 1) : d331607 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d36314, d331607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36314, d331607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36315 q = 1) (hb : d331335 q = 1) : d331608 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d36315, d331608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36315, d331608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d269998 q = 1) (hb : d331335 q = 1) : d331698 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269998, d331698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90453 q ha hb
    | true =>
      simp only [d269998, d331698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90460 q ha hb
  have h7 (q : Pattern) (ha : d36467 q = 1) (hb : d331335 q = 1) : d331711 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36467, d331711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90434 q ha hb
    | true =>
      simp only [d36467, d331711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90435 q ha hb
  have h8 (q : Pattern) (ha : d269999 q = 1) (hb : d331335 q = 1) : d331712 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d269999, d331712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d269999, d331712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d270000 q = 1) (hb : d331335 q = 1) : d331713 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270000, d331713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d270000, d331713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d270001 q = 1) (hb : d331335 q = 1) : d331714 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270001, d331714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d270001, d331714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d270005 q = 1) (hb : d331335 q = 1) : d331718 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270005, d331718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270005, d331718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90461 q ha hb
  have h12 (q : Pattern) (ha : d36476 q = 1) (hb : d331335 q = 1) : d331720 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36476, d331720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36476, d331720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90436 q ha hb
  have h13 (q : Pattern) (ha : d270006 q = 1) (hb : d331335 q = 1) : d331721 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270006, d331721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d270006, d331721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d270007 q = 1) (hb : d331335 q = 1) : d331722 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270007, d331722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d270007, d331722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d270008 q = 1) (hb : d331335 q = 1) : d331723 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270008, d331723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d270008, d331723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d270009 q = 1) (hb : d331335 q = 1) : d331724 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270009, d331724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d270009, d331724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d270015 q = 1) (hb : d331335 q = 1) : d331781 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d270015, d331781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270015, d331781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90469 q ha hb
  have h18 (q : Pattern) (ha : d36581 q = 1) (hb : d331335 q = 1) : d331792 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d36581, d331792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36581, d331792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90439 q ha hb
  have h19 (q : Pattern) (ha : d270016 q = 1) (hb : d331335 q = 1) : d331793 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270016, d331793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d270016, d331793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d270017 q = 1) (hb : d331335 q = 1) : d331794 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d270017, d331794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d270017, d331794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d270018 q = 1) (hb : d331335 q = 1) : d331795 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d270018, d331795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d270018, d331795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d270019 q = 1) (hb : d331335 q = 1) : d331796 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d270019, d331796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d270019, d331796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d270020 q = 1) (hb : d331335 q = 1) : d331797 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d270020, d331797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d270020, d331797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro90471 (p : Pattern) (ha : d270026 p = 1) (hb : d331335 p = 1) : d331803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d270021 q = 1) (hb : d331335 q = 1) : d331798 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d270021, d331798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270021, d331798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90470 q ha hb
  have h2 (q : Pattern) (ha : d270022 q = 1) (hb : d331335 q = 1) : d331799 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d270022, d331799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270022, d331799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d270023 q = 1) (hb : d331335 q = 1) : d331800 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d270023, d331800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270023, d331800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d270024 q = 1) (hb : d331335 q = 1) : d331801 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d270024, d331801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270024, d331801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d270025 q = 1) (hb : d331335 q = 1) : d331802 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d270025, d331802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270025, d331802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d270026 q = 1) (hb : d331335 q = 1) : d331803 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d270026, d331803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d270026, d331803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90472 (p : Pattern) (ha : d36594 p = 1) (hb : d331335 p = 1) : d331805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9452 q = 1) (hb : d331335 q = 1) : d331337 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d331337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90386 q ha hb
    | true =>
      simp only [d9452, d331337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9453 q = 1) (hb : d331335 q = 1) : d331338 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d331338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9453, d331338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d331335 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9454 q = 1) (hb : d331335 q = 1) : d331339 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9454, d331339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9454, d331339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21 q = 1) (hb : d331335 q = 1) : d21 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d36005 q = 1) (hb : d331335 q = 1) : d331340 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36005, d331340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36005, d331340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36006 q = 1) (hb : d331335 q = 1) : d331341 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36006, d331341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36006, d331341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36594 q = 1) (hb : d331335 q = 1) : d331805 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d36594, d331805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36594, d331805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro90473 (p : Pattern) (ha : d36600 p = 1) (hb : d331335 p = 1) : d331811 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36341 q = 1) (hb : d331335 q = 1) : d331630 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36341, d331630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90445 q ha hb
    | true =>
      simp only [d36341, d331630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36342 q = 1) (hb : d331335 q = 1) : d331631 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36342, d331631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36342, d331631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36343 q = 1) (hb : d331335 q = 1) : d331632 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36343, d331632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36343, d331632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36344 q = 1) (hb : d331335 q = 1) : d331633 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36344, d331633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36344, d331633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36346 q = 1) (hb : d331335 q = 1) : d331635 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36346, d331635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90446 q ha hb
    | true =>
      simp only [d36346, d331635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36347 q = 1) (hb : d331335 q = 1) : d331636 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36347, d331636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36347, d331636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36348 q = 1) (hb : d331335 q = 1) : d331637 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36348, d331637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36348, d331637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36349 q = 1) (hb : d331335 q = 1) : d331638 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36349, d331638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36349, d331638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36350 q = 1) (hb : d331335 q = 1) : d331639 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36350, d331639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36350, d331639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36354 q = 1) (hb : d331335 q = 1) : d331643 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36354, d331643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90447 q ha hb
    | true =>
      simp only [d36354, d331643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36355 q = 1) (hb : d331335 q = 1) : d331644 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36355, d331644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36355, d331644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d36356 q = 1) (hb : d331335 q = 1) : d331645 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36356, d331645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36356, d331645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d36357 q = 1) (hb : d331335 q = 1) : d331646 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36357, d331646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d36357, d331646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d36595 q = 1) (hb : d331335 q = 1) : d331806 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36595, d331806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90472 q ha hb
    | true =>
      simp only [d36595, d331806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d36596 q = 1) (hb : d331335 q = 1) : d331807 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36596, d331807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d36596, d331807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d36597 q = 1) (hb : d331335 q = 1) : d331808 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36597, d331808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36597, d331808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d36598 q = 1) (hb : d331335 q = 1) : d331809 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36598, d331809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d36598, d331809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d36599 q = 1) (hb : d331335 q = 1) : d331810 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36599, d331810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36599, d331810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d36600 q = 1) (hb : d331335 q = 1) : d331811 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36600, d331811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36600, d331811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro90474 (p : Pattern) (ha : d36603 p = 1) (hb : d331335 p = 1) : d331814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36121 q = 1) (hb : d331335 q = 1) : d331455 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36121, d331455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90406 q ha hb
    | true =>
      simp only [d36121, d331455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36122 q = 1) (hb : d331335 q = 1) : d331456 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36122, d331456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36122, d331456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36123 q = 1) (hb : d331335 q = 1) : d331457 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36123, d331457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36123, d331457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36124 q = 1) (hb : d331335 q = 1) : d331458 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36124, d331458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36124, d331458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36595 q = 1) (hb : d331335 q = 1) : d331806 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36595, d331806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90472 q ha hb
    | true =>
      simp only [d36595, d331806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36596 q = 1) (hb : d331335 q = 1) : d331807 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36596, d331807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36596, d331807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36597 q = 1) (hb : d331335 q = 1) : d331808 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36597, d331808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36597, d331808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36598 q = 1) (hb : d331335 q = 1) : d331809 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36598, d331809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36598, d331809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36601 q = 1) (hb : d331335 q = 1) : d331812 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36601, d331812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36601, d331812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36602 q = 1) (hb : d331335 q = 1) : d331813 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36602, d331813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36602, d331813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36603 q = 1) (hb : d331335 q = 1) : d331814 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36603, d331814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36603, d331814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro90475 (p : Pattern) (ha : d36607 p = 1) (hb : d331335 p = 1) : d331818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36595 q = 1) (hb : d331335 q = 1) : d331806 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36595, d331806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90472 q ha hb
    | true =>
      simp only [d36595, d331806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36596 q = 1) (hb : d331335 q = 1) : d331807 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36596, d331807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36596, d331807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36597 q = 1) (hb : d331335 q = 1) : d331808 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36597, d331808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36597, d331808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36598 q = 1) (hb : d331335 q = 1) : d331809 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36598, d331809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36598, d331809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36602 q = 1) (hb : d331335 q = 1) : d331813 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36602, d331813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36602, d331813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36607 q = 1) (hb : d331335 q = 1) : d331818 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36607, d331818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36607, d331818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90476 (p : Pattern) (ha : d36614 p = 1) (hb : d331335 p = 1) : d331825 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36604 q = 1) (hb : d331335 q = 1) : d331815 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36604, d331815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90473 q ha hb
    | true =>
      simp only [d36604, d331815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90474 q ha hb
  have h2 (q : Pattern) (ha : d36605 q = 1) (hb : d331335 q = 1) : d331816 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36605, d331816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36605, d331816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36606 q = 1) (hb : d331335 q = 1) : d331817 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36606, d331817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36606, d331817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36608 q = 1) (hb : d331335 q = 1) : d331819 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36608, d331819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90474 q ha hb
    | true =>
      simp only [d36608, d331819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90475 q ha hb
  have h5 (q : Pattern) (ha : d36609 q = 1) (hb : d331335 q = 1) : d331820 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36609, d331820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36609, d331820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36610 q = 1) (hb : d331335 q = 1) : d331821 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36610, d331821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36610, d331821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36611 q = 1) (hb : d331335 q = 1) : d331822 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36611, d331822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36611, d331822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36612 q = 1) (hb : d331335 q = 1) : d331823 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36612, d331823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36612, d331823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36613 q = 1) (hb : d331335 q = 1) : d331824 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36613, d331824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36613, d331824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36614 q = 1) (hb : d331335 q = 1) : d331825 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36614, d331825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36614, d331825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro90477 (p : Pattern) (ha : d36618 p = 1) (hb : d331335 p = 1) : d331829 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36608 q = 1) (hb : d331335 q = 1) : d331819 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36608, d331819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90474 q ha hb
    | true =>
      simp only [d36608, d331819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90475 q ha hb
  have h2 (q : Pattern) (ha : d36609 q = 1) (hb : d331335 q = 1) : d331820 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36609, d331820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36609, d331820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36610 q = 1) (hb : d331335 q = 1) : d331821 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36610, d331821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36610, d331821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36612 q = 1) (hb : d331335 q = 1) : d331823 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36612, d331823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36612, d331823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36617 q = 1) (hb : d331335 q = 1) : d331828 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36617, d331828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36617, d331828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36618 q = 1) (hb : d331335 q = 1) : d331829 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36618, d331829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36618, d331829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90478 (p : Pattern) (ha : d36624 p = 1) (hb : d331335 p = 1) : d331835 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36615 q = 1) (hb : d331335 q = 1) : d331826 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36615, d331826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90476 q ha hb
    | true =>
      simp only [d36615, d331826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36616 q = 1) (hb : d331335 q = 1) : d331827 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36616, d331827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36616, d331827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36619 q = 1) (hb : d331335 q = 1) : d331830 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36619, d331830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90477 q ha hb
    | true =>
      simp only [d36619, d331830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36620 q = 1) (hb : d331335 q = 1) : d331831 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36620, d331831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36620, d331831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36621 q = 1) (hb : d331335 q = 1) : d331832 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36621, d331832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36621, d331832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36622 q = 1) (hb : d331335 q = 1) : d331833 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36622, d331833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36622, d331833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36623 q = 1) (hb : d331335 q = 1) : d331834 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36623, d331834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36623, d331834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36624 q = 1) (hb : d331335 q = 1) : d331835 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36624, d331835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36624, d331835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90479 (p : Pattern) (ha : d36628 p = 1) (hb : d331335 p = 1) : d331839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36619 q = 1) (hb : d331335 q = 1) : d331830 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36619, d331830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90477 q ha hb
    | true =>
      simp only [d36619, d331830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36620 q = 1) (hb : d331335 q = 1) : d331831 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36620, d331831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36620, d331831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36625 q = 1) (hb : d331335 q = 1) : d331836 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36625, d331836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36625, d331836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36626 q = 1) (hb : d331335 q = 1) : d331837 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36626, d331837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36626, d331837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36627 q = 1) (hb : d331335 q = 1) : d331838 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36627, d331838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36627, d331838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36628 q = 1) (hb : d331335 q = 1) : d331839 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36628, d331839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36628, d331839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90480 (p : Pattern) (ha : d36634 p = 1) (hb : d331335 p = 1) : d331845 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36629 q = 1) (hb : d331335 q = 1) : d331840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36629, d331840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90478 q ha hb
    | true =>
      simp only [d36629, d331840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90479 q ha hb
  have h2 (q : Pattern) (ha : d36630 q = 1) (hb : d331335 q = 1) : d331841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36630, d331841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36630, d331841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36631 q = 1) (hb : d331335 q = 1) : d331842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36631, d331842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36631, d331842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36632 q = 1) (hb : d331335 q = 1) : d331843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36632, d331843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36632, d331843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36633 q = 1) (hb : d331335 q = 1) : d331844 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36633, d331844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36633, d331844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36634 q = 1) (hb : d331335 q = 1) : d331845 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36634, d331845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36634, d331845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90481 (p : Pattern) (ha : d36637 p = 1) (hb : d331335 p = 1) : d331848 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36615 q = 1) (hb : d331335 q = 1) : d331826 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36615, d331826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90476 q ha hb
    | true =>
      simp only [d36615, d331826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36616 q = 1) (hb : d331335 q = 1) : d331827 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36616, d331827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36616, d331827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36619 q = 1) (hb : d331335 q = 1) : d331830 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36619, d331830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90477 q ha hb
    | true =>
      simp only [d36619, d331830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36620 q = 1) (hb : d331335 q = 1) : d331831 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36620, d331831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36620, d331831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36621 q = 1) (hb : d331335 q = 1) : d331832 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36621, d331832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36621, d331832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36622 q = 1) (hb : d331335 q = 1) : d331833 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36622, d331833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36622, d331833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36623 q = 1) (hb : d331335 q = 1) : d331834 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36623, d331834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36623, d331834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36637 q = 1) (hb : d331335 q = 1) : d331848 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36637, d331848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36637, d331848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro90482 (p : Pattern) (ha : d36638 p = 1) (hb : d331335 p = 1) : d331849 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36619 q = 1) (hb : d331335 q = 1) : d331830 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36619, d331830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90477 q ha hb
    | true =>
      simp only [d36619, d331830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36620 q = 1) (hb : d331335 q = 1) : d331831 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36620, d331831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36620, d331831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36625 q = 1) (hb : d331335 q = 1) : d331836 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36625, d331836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36625, d331836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36626 q = 1) (hb : d331335 q = 1) : d331837 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36626, d331837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36626, d331837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36627 q = 1) (hb : d331335 q = 1) : d331838 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36627, d331838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36627, d331838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36638 q = 1) (hb : d331335 q = 1) : d331849 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36638, d331849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36638, d331849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90483 (p : Pattern) (ha : d36644 p = 1) (hb : d331335 p = 1) : d331855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36629 q = 1) (hb : d331335 q = 1) : d331840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36629, d331840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90478 q ha hb
    | true =>
      simp only [d36629, d331840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90479 q ha hb
  have h2 (q : Pattern) (ha : d36630 q = 1) (hb : d331335 q = 1) : d331841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36630, d331841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36630, d331841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36631 q = 1) (hb : d331335 q = 1) : d331842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36631, d331842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36631, d331842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36632 q = 1) (hb : d331335 q = 1) : d331843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36632, d331843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36632, d331843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36633 q = 1) (hb : d331335 q = 1) : d331844 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36633, d331844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36633, d331844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36639 q = 1) (hb : d331335 q = 1) : d331850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36639, d331850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90481 q ha hb
    | true =>
      simp only [d36639, d331850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90482 q ha hb
  have h7 (q : Pattern) (ha : d36640 q = 1) (hb : d331335 q = 1) : d331851 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36640, d331851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36640, d331851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36641 q = 1) (hb : d331335 q = 1) : d331852 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36641, d331852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36641, d331852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36642 q = 1) (hb : d331335 q = 1) : d331853 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36642, d331853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36642, d331853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36643 q = 1) (hb : d331335 q = 1) : d331854 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36643, d331854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36643, d331854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36644 q = 1) (hb : d331335 q = 1) : d331855 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36644, d331855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36644, d331855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro90484 (p : Pattern) (ha : d36811 p = 1) (hb : d331335 p = 1) : d331960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36629 q = 1) (hb : d331335 q = 1) : d331840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36629, d331840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90478 q ha hb
    | true =>
      simp only [d36629, d331840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90479 q ha hb
  have h2 (q : Pattern) (ha : d36630 q = 1) (hb : d331335 q = 1) : d331841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36630, d331841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36630, d331841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36631 q = 1) (hb : d331335 q = 1) : d331842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36631, d331842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36631, d331842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36632 q = 1) (hb : d331335 q = 1) : d331843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36632, d331843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36632, d331843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36633 q = 1) (hb : d331335 q = 1) : d331844 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36633, d331844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36633, d331844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36806 q = 1) (hb : d331335 q = 1) : d331955 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36806, d331955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90479 q ha hb
    | true =>
      simp only [d36806, d331955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36807 q = 1) (hb : d331335 q = 1) : d331956 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36807, d331956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36807, d331956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36808 q = 1) (hb : d331335 q = 1) : d331957 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36808, d331957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36808, d331957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36809 q = 1) (hb : d331335 q = 1) : d331958 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36809, d331958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36809, d331958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36810 q = 1) (hb : d331335 q = 1) : d331959 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36810, d331959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36810, d331959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36811 q = 1) (hb : d331335 q = 1) : d331960 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36811, d331960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36811, d331960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro90485 (p : Pattern) (ha : d36817 p = 1) (hb : d331335 p = 1) : d331966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36806 q = 1) (hb : d331335 q = 1) : d331955 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36806, d331955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90479 q ha hb
    | true =>
      simp only [d36806, d331955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36807 q = 1) (hb : d331335 q = 1) : d331956 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36807, d331956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36807, d331956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36808 q = 1) (hb : d331335 q = 1) : d331957 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36808, d331957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36808, d331957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36809 q = 1) (hb : d331335 q = 1) : d331958 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36809, d331958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36809, d331958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36810 q = 1) (hb : d331335 q = 1) : d331959 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36810, d331959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36810, d331959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36812 q = 1) (hb : d331335 q = 1) : d331961 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36812, d331961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90482 q ha hb
    | true =>
      simp only [d36812, d331961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36813 q = 1) (hb : d331335 q = 1) : d331962 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36813, d331962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36813, d331962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36814 q = 1) (hb : d331335 q = 1) : d331963 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36814, d331963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36814, d331963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36815 q = 1) (hb : d331335 q = 1) : d331964 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36815, d331964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36815, d331964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36816 q = 1) (hb : d331335 q = 1) : d331965 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36816, d331965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36816, d331965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d36817 q = 1) (hb : d331335 q = 1) : d331966 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36817, d331966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36817, d331966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro90486 (p : Pattern) (ha : d36826 p = 1) (hb : d331335 p = 1) : d331975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36812 q = 1) (hb : d331335 q = 1) : d331961 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36812, d331961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90482 q ha hb
    | true =>
      simp only [d36812, d331961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36813 q = 1) (hb : d331335 q = 1) : d331962 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36813, d331962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36813, d331962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36814 q = 1) (hb : d331335 q = 1) : d331963 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36814, d331963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36814, d331963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36815 q = 1) (hb : d331335 q = 1) : d331964 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36815, d331964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36815, d331964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36816 q = 1) (hb : d331335 q = 1) : d331965 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36816, d331965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36816, d331965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36826 q = 1) (hb : d331335 q = 1) : d331975 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36826, d331975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36826, d331975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90487 (p : Pattern) (ha : d36863 p = 1) (hb : d331335 p = 1) : d332012 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36214 q = 1) (hb : d331335 q = 1) : d331526 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36214, d331526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36214, d331526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90406 q ha hb
  have h2 (q : Pattern) (ha : d36121 q = 1) (hb : d331335 q = 1) : d331455 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36121, d331455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90406 q ha hb
    | true =>
      simp only [d36121, d331455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36215 q = 1) (hb : d331335 q = 1) : d331527 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36215, d331527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36215, d331527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36122 q = 1) (hb : d331335 q = 1) : d331456 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36122, d331456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36122, d331456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36216 q = 1) (hb : d331335 q = 1) : d331528 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36216, d331528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36216, d331528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36217 q = 1) (hb : d331335 q = 1) : d331529 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36217, d331529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36217, d331529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36847 q = 1) (hb : d331335 q = 1) : d331996 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36847, d331996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36847, d331996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90472 q ha hb
  have h8 (q : Pattern) (ha : d36595 q = 1) (hb : d331335 q = 1) : d331806 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36595, d331806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90472 q ha hb
    | true =>
      simp only [d36595, d331806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d36848 q = 1) (hb : d331335 q = 1) : d331997 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36848, d331997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36848, d331997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36596 q = 1) (hb : d331335 q = 1) : d331807 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36596, d331807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36596, d331807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d36849 q = 1) (hb : d331335 q = 1) : d331998 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36849, d331998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36849, d331998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d36850 q = 1) (hb : d331335 q = 1) : d331999 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36850, d331999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d36850, d331999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d36862 q = 1) (hb : d331335 q = 1) : d332011 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36862, d332011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36862, d332011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d36856 q = 1) (hb : d331335 q = 1) : d332005 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36856, d332005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d36856, d332005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d36863 q = 1) (hb : d331335 q = 1) : d332012 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36863, d332012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d36863, d332012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro90488 (p : Pattern) (ha : d36867 p = 1) (hb : d331335 p = 1) : d332016 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36847 q = 1) (hb : d331335 q = 1) : d331996 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36847, d331996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36847, d331996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90472 q ha hb
  have h2 (q : Pattern) (ha : d36595 q = 1) (hb : d331335 q = 1) : d331806 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d36595, d331806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90472 q ha hb
    | true =>
      simp only [d36595, d331806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36848 q = 1) (hb : d331335 q = 1) : d331997 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36848, d331997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36848, d331997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36596 q = 1) (hb : d331335 q = 1) : d331807 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d36596, d331807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36596, d331807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36849 q = 1) (hb : d331335 q = 1) : d331998 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d36849, d331998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36849, d331998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36850 q = 1) (hb : d331335 q = 1) : d331999 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d36850, d331999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36850, d331999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36856 q = 1) (hb : d331335 q = 1) : d332005 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d36856, d332005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36856, d332005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36867 q = 1) (hb : d331335 q = 1) : d332016 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d36867, d332016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36867, d332016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro90489 (p : Pattern) (ha : d36886 p = 1) (hb : d331335 p = 1) : d332035 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36868 q = 1) (hb : d331335 q = 1) : d332017 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d36868, d332017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90487 q ha hb
    | true =>
      simp only [d36868, d332017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90488 q ha hb
  have h2 (q : Pattern) (ha : d36869 q = 1) (hb : d331335 q = 1) : d332018 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d36869, d332018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36869, d332018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36870 q = 1) (hb : d331335 q = 1) : d332019 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d36870, d332019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36870, d332019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d36876 q = 1) (hb : d331335 q = 1) : d332025 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d36876, d332025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36876, d332025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36885 q = 1) (hb : d331335 q = 1) : d332034 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d36885, d332034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36885, d332034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36886 q = 1) (hb : d331335 q = 1) : d332035 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36886, d332035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36886, d332035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90490 (p : Pattern) (ha : d36957 p = 1) (hb : d331335 p = 1) : d332058 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36887 q = 1) (hb : d331335 q = 1) : d332036 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36887, d332036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90489 q ha hb
    | true =>
      simp only [d36887, d332036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36888 q = 1) (hb : d331335 q = 1) : d332037 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36888, d332037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36888, d332037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36954 q = 1) (hb : d331335 q = 1) : d332055 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36954, d332055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36954, d332055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36955 q = 1) (hb : d331335 q = 1) : d332056 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36955, d332056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36955, d332056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36956 q = 1) (hb : d331335 q = 1) : d332057 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36956, d332057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36956, d332057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36957 q = 1) (hb : d331335 q = 1) : d332058 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36957, d332058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36957, d332058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro90491 (p : Pattern) (ha : d36963 p = 1) (hb : d331335 p = 1) : d332064 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36958 q = 1) (hb : d331335 q = 1) : d332059 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d36958, d332059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90490 q ha hb
    | true =>
      simp only [d36958, d332059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36959 q = 1) (hb : d331335 q = 1) : d332060 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d36959, d332060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36959, d332060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36960 q = 1) (hb : d331335 q = 1) : d332061 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d36960, d332061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36960, d332061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36961 q = 1) (hb : d331335 q = 1) : d332062 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d36961, d332062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36961, d332062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36962 q = 1) (hb : d331335 q = 1) : d332063 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d36962, d332063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36962, d332063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36963 q = 1) (hb : d331335 q = 1) : d332064 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d36963, d332064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36963, d332064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90492 (p : Pattern) (ha : d36649 p = 1) (hb : d331335 p = 1) : d331860 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36615 q = 1) (hb : d331335 q = 1) : d331826 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36615, d331826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90476 q ha hb
    | true =>
      simp only [d36615, d331826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36616 q = 1) (hb : d331335 q = 1) : d331827 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36616, d331827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36616, d331827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36619 q = 1) (hb : d331335 q = 1) : d331830 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36619, d331830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90477 q ha hb
    | true =>
      simp only [d36619, d331830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36620 q = 1) (hb : d331335 q = 1) : d331831 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36620, d331831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36620, d331831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36621 q = 1) (hb : d331335 q = 1) : d331832 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36621, d331832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36621, d331832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36622 q = 1) (hb : d331335 q = 1) : d331833 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36622, d331833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36622, d331833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36648 q = 1) (hb : d331335 q = 1) : d331859 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36648, d331859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36648, d331859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d36649 q = 1) (hb : d331335 q = 1) : d331860 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36649, d331860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36649, d331860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90493 (p : Pattern) (ha : d36651 p = 1) (hb : d331335 p = 1) : d331862 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36619 q = 1) (hb : d331335 q = 1) : d331830 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36619, d331830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90477 q ha hb
    | true =>
      simp only [d36619, d331830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36620 q = 1) (hb : d331335 q = 1) : d331831 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36620, d331831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36620, d331831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36625 q = 1) (hb : d331335 q = 1) : d331836 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36625, d331836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36625, d331836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36626 q = 1) (hb : d331335 q = 1) : d331837 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36626, d331837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36626, d331837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36650 q = 1) (hb : d331335 q = 1) : d331861 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36650, d331861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36650, d331861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36651 q = 1) (hb : d331335 q = 1) : d331862 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36651, d331862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36651, d331862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90494 (p : Pattern) (ha : d36658 p = 1) (hb : d331335 p = 1) : d331869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36615 q = 1) (hb : d331335 q = 1) : d331826 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36615, d331826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90476 q ha hb
    | true =>
      simp only [d36615, d331826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36616 q = 1) (hb : d331335 q = 1) : d331827 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36616, d331827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36616, d331827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36619 q = 1) (hb : d331335 q = 1) : d331830 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36619, d331830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90477 q ha hb
    | true =>
      simp only [d36619, d331830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36620 q = 1) (hb : d331335 q = 1) : d331831 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36620, d331831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36620, d331831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36621 q = 1) (hb : d331335 q = 1) : d331832 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36621, d331832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36621, d331832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36656 q = 1) (hb : d331335 q = 1) : d331867 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36656, d331867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36656, d331867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d36657 q = 1) (hb : d331335 q = 1) : d331868 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36657, d331868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36657, d331868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36658 q = 1) (hb : d331335 q = 1) : d331869 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36658, d331869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36658, d331869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro90495 (p : Pattern) (ha : d36661 p = 1) (hb : d331335 p = 1) : d331872 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36619 q = 1) (hb : d331335 q = 1) : d331830 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d36619, d331830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90477 q ha hb
    | true =>
      simp only [d36619, d331830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36620 q = 1) (hb : d331335 q = 1) : d331831 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d36620, d331831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36620, d331831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d36625 q = 1) (hb : d331335 q = 1) : d331836 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d36625, d331836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36625, d331836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36659 q = 1) (hb : d331335 q = 1) : d331870 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d36659, d331870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36659, d331870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d36660 q = 1) (hb : d331335 q = 1) : d331871 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d36660, d331871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36660, d331871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d36661 q = 1) (hb : d331335 q = 1) : d331872 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d36661, d331872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36661, d331872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro90496 (p : Pattern) (ha : d36665 p = 1) (hb : d331335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d331334 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d307 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d14, d307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14 q = 1) (hb : d309 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d825 q = 1) (hb : d253504 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d825, d253504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d825, d253504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h11 (q : Pattern) (ha : d36333 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d36333, d331335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36333, d331335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d36665 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d36665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d36665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro90497 (p : Pattern) (ha : d36671 p = 1) (hb : d331335 p = 1) : d331878 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36666 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d36666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90496 q ha hb
    | true =>
      simp only [d36666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36667 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d36667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36335 q = 1) (hb : d331335 q = 1) : d43407 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d36335, d43407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90444 q ha hb
    | true =>
      simp only [d36335, d43407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36336 q = 1) (hb : d331335 q = 1) : d43408 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d36336, d43408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36336, d43408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36668 q = 1) (hb : d331335 q = 1) : d43409 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d36668, d43409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36668, d43409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d36115 q = 1) (hb : d331335 q = 1) : d331449 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d36115, d331449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90405 q ha hb
    | true =>
      simp only [d36115, d331449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d36116 q = 1) (hb : d331335 q = 1) : d331450 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d36116, d331450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d36116, d331450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36337 q = 1) (hb : d331335 q = 1) : d331626 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d36337, d331626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36337, d331626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36669 q = 1) (hb : d331335 q = 1) : d331876 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36669, d331876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36669, d331876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36670 q = 1) (hb : d331335 q = 1) : d331877 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36670, d331877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36670, d331877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9452 q = 1) (hb : d331335 q = 1) : d331337 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d331337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90386 q ha hb
    | true =>
      simp only [d9452, d331337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9453 q = 1) (hb : d331335 q = 1) : d331338 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d331338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9453, d331338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d36117 q = 1) (hb : d331335 q = 1) : d331451 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d36117, d331451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d36117, d331451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d36338 q = 1) (hb : d331335 q = 1) : d331627 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36338, d331627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d36338, d331627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d36339 q = 1) (hb : d331335 q = 1) : d331628 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36339, d331628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d36339, d331628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d36671 q = 1) (hb : d331335 q = 1) : d331878 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d36671, d331878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36671, d331878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro90498 (p : Pattern) (ha : d9580 p = 1) (hb : d331335 p = 1) : d331883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d307 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d307, d271213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d307, d271213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d271213 q = 1) : d308 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309 q = 1) (hb : d271213 q = 1) : d1523 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, d1523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309, d1523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d825 q = 1) (hb : d331334 q = 1) : d2005 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d825, d331334, d2005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d825, d331334, d2005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d253504 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5121 q = 1) (hb : d331335 q = 1) : d2006 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d5121, d331335, d2006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5121, d331335, d2006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9579 q = 1) (hb : d331335 q = 1) : d9579 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9580 q = 1) (hb : d331335 q = 1) : d331883 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d9580, d331883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9580, d331883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro90499 (p : Pattern) (ha : d36676 p = 1) (hb : d331335 p = 1) : d331889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d331335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d36335 q = 1) (hb : d331335 q = 1) : d43407 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d36335, d43407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90444 q ha hb
    | true =>
      simp only [d36335, d43407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d36336 q = 1) (hb : d331335 q = 1) : d43408 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d36336, d43408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d36336, d43408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d36115 q = 1) (hb : d331335 q = 1) : d331449 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d36115, d331449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90405 q ha hb
    | true =>
      simp only [d36115, d331449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d36116 q = 1) (hb : d331335 q = 1) : d331450 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d36116, d331450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d36116, d331450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d36337 q = 1) (hb : d331335 q = 1) : d331626 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d36337, d331626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d36337, d331626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9452 q = 1) (hb : d331335 q = 1) : d331337 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d331337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90386 q ha hb
    | true =>
      simp only [d9452, d331337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9453 q = 1) (hb : d331335 q = 1) : d331338 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d331338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9453, d331338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d36117 q = 1) (hb : d331335 q = 1) : d331451 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d36117, d331451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d36117, d331451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d36338 q = 1) (hb : d331335 q = 1) : d331627 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d36338, d331627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36338, d331627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d36339 q = 1) (hb : d331335 q = 1) : d331628 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d36339, d331628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d36339, d331628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9581 q = 1) (hb : d331335 q = 1) : d331884 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9581, d331884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90498 q ha hb
    | true =>
      simp only [d9581, d331884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9582 q = 1) (hb : d331335 q = 1) : d331885 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9582, d331885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9582, d331885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d9583 q = 1) (hb : d331335 q = 1) : d331886 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9583, d331886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9583, d331886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h14 (q : Pattern) (ha : d9584 q = 1) (hb : d331335 q = 1) : d331887 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9584, d331887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9584, d331887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9585 q = 1) (hb : d331335 q = 1) : d331888 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9585, d331888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9585, d331888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d36676 q = 1) (hb : d331335 q = 1) : d331889 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d36676, d331889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d36676, d331889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
end NetHack.Soko22Hazard87
