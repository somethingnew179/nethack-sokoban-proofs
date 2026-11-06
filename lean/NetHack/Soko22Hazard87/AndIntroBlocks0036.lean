import NetHack.Soko22Hazard87.AndIntroBlocks0035
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro9000 (p : Pattern) (ha : d77526 p = 1) (hb : d81898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77521 q = 1) (hb : d81893 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77521, d81893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77521, d81893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8999 q ha hb
  have h2 (q : Pattern) (ha : d77522 q = 1) (hb : d81894 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77522, d81894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77522, d81894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77523 q = 1) (hb : d81895 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77523, d81895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77523, d81895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77524 q = 1) (hb : d81896 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77524, d81896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77524, d81896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77525 q = 1) (hb : d81897 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77525, d81897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77525, d81897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77526 q = 1) (hb : d81898 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77526, d81898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77526, d81898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9001 (p : Pattern) (ha : d5264 p = 1) (hb : d81915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5259 q = 1) (hb : d69343 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5259, d69343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7982 q ha hb
    | true =>
      simp only [d5259, d69343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5260 q = 1) (hb : d69344 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5260, d69344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5260, d69344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5261 q = 1) (hb : d81912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5261, d81912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5261, d81912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5262 q = 1) (hb : d81913 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5262, d81913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5262, d81913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5263 q = 1) (hb : d81914 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5263, d81914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5263, d81914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5264 q = 1) (hb : d81915 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5264, d81915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5264, d81915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9002 (p : Pattern) (ha : d5270 p = 1) (hb : d81936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53385 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5265 q = 1) (hb : d81931 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5265, d81931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9001 q ha hb
    | true =>
      simp only [d5265, d81931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5266 q = 1) (hb : d81932 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5266, d81932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5266, d81932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5267 q = 1) (hb : d81933 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d5267, d81933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5267, d81933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5268 q = 1) (hb : d81934 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d5268, d81934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5268, d81934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5269 q = 1) (hb : d81935 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d5269, d81935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5269, d81935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2305 q = 1) (hb : d53470 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
    | true =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2306 q = 1) (hb : d53471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2307 q = 1) (hb : d53472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2308 q = 1) (hb : d53473 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2309 q = 1) (hb : d53474 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5270 q = 1) (hb : d81936 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d5270, d81936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5270, d81936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro9003 (p : Pattern) (ha : d6550 p = 1) (hb : d53381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro273 q ha hb
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6547 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6547, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6548 q = 1) (hb : d53379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6548, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6549 q = 1) (hb : d53380 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6549, d53380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6549, d53380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6550 q = 1) (hb : d53381 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6550, d53381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6550, d53381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9004 (p : Pattern) (ha : d53391 p = 1) (hb : d77535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53385 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6592 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9003 q ha hb
    | true =>
      simp only [d6592, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53387 q = 1) (hb : d77531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53387, d77531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53387, d77531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d53388 q = 1) (hb : d77532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53388, d77532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53388, d77532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53389 q = 1) (hb : d77533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53389, d77533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53389, d77533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53390 q = 1) (hb : d77534 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53390, d77534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53390, d77534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53391 q = 1) (hb : d77535 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53391, d77535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53391, d77535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9005 (p : Pattern) (ha : d6559 p = 1) (hb : d53394 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro273 q ha hb
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6547 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6547, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6548 q = 1) (hb : d53379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6548, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6549 q = 1) (hb : d53380 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6549, d53380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6549, d53380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6559 q = 1) (hb : d53394 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6559, d53394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6559, d53394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro9006 (p : Pattern) (ha : d53401 p = 1) (hb : d77542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53385 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6592 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9003 q ha hb
    | true =>
      simp only [d6592, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53387 q = 1) (hb : d77531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53387, d77531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53387, d77531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d53388 q = 1) (hb : d77532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53388, d77532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53388, d77532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53389 q = 1) (hb : d77533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53389, d77533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53389, d77533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53390 q = 1) (hb : d77534 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53390, d77534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53390, d77534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53395 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6613 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9005 q ha hb
    | true =>
      simp only [d6613, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53397 q = 1) (hb : d77538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53397, d77538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53397, d77538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53398 q = 1) (hb : d77539 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53398, d77539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53398, d77539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d53399 q = 1) (hb : d77540 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53399, d77540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53399, d77540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53400 q = 1) (hb : d77541 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53400, d77541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53400, d77541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53401 q = 1) (hb : d77542 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53401, d77542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53401, d77542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro9007 (p : Pattern) (ha : d6607 p = 1) (hb : d81922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2156 q = 1) (hb : d53435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2156, d53435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro291 q ha hb
    | true =>
      simp only [d2156, d53435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2157 q = 1) (hb : d53436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2157, d53436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2157, d53436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81907 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6581 q = 1) (hb : d81908 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6581, d81908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6581, d81908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6582 q = 1) (hb : d81909 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6582, d81909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6582, d81909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6583 q = 1) (hb : d81910 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6583, d81910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6583, d81910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6607 q = 1) (hb : d81922 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6607, d81922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6607, d81922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro9008 (p : Pattern) (ha : d76711 p = 1) (hb : d81943 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81923 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d76701 q = 1) (hb : d81924 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76701, d81924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9007 q ha hb
    | true =>
      simp only [d76701, d81924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d76702 q = 1) (hb : d81925 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76702, d81925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76702, d81925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6613 q = 1) (hb : d76331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d76331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7561 q ha hb
    | true =>
      simp only [d6613, d76331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6614 q = 1) (hb : d76332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6614, d76332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6614, d76332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d76703 q = 1) (hb : d81926 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76703, d81926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76703, d81926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76704 q = 1) (hb : d81941 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76704, d81941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76704, d81941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76705 q = 1) (hb : d81942 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76705, d81942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76705, d81942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76711 q = 1) (hb : d81943 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76711, d81943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76711, d81943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro9009 (p : Pattern) (ha : d6641 p = 1) (hb : d81957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2373 q = 1) (hb : d53538 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2373, d53538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro296 q ha hb
    | true =>
      simp only [d2373, d53538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2374 q = 1) (hb : d53539 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2374, d53539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2374, d53539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81953 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6638 q = 1) (hb : d81954 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6638, d81954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6638, d81954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6639 q = 1) (hb : d81955 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6639, d81955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6639, d81955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6640 q = 1) (hb : d81956 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6640, d81956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6640, d81956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6641 q = 1) (hb : d81957 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6641, d81957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6641, d81957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro9010 (p : Pattern) (ha : d76722 p = 1) (hb : d81967 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81961 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d76717 q = 1) (hb : d81962 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76717, d81962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9009 q ha hb
    | true =>
      simp only [d76717, d81962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53562 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d76718 q = 1) (hb : d81963 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76718, d81963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d76718, d81963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6672 q = 1) (hb : d76386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6672, d76386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7566 q ha hb
    | true =>
      simp only [d6672, d76386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6673 q = 1) (hb : d76387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6673, d76387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6673, d76387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d76719 q = 1) (hb : d81964 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76719, d81964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76719, d81964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76720 q = 1) (hb : d81965 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d76720, d81965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76720, d81965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d76721 q = 1) (hb : d81966 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d76721, d81966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76721, d81966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76722 q = 1) (hb : d81967 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d76722, d81967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76722, d81967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro9011 (p : Pattern) (ha : d6570 p = 1) (hb : d53406 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro273 q ha hb
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6547 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6547, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6548 q = 1) (hb : d53379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6548, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6569 q = 1) (hb : d53405 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6569, d53405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6569, d53405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6570 q = 1) (hb : d53406 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6570, d53406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6570, d53406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9012 (p : Pattern) (ha : d6577 p = 1) (hb : d53415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro273 q ha hb
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6547 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6547, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6575 q = 1) (hb : d53413 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6575, d53413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6575, d53413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6576 q = 1) (hb : d53414 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6576, d53414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6576, d53414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6577 q = 1) (hb : d53415 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6577, d53415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6577, d53415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9013 (p : Pattern) (ha : d6584 p = 1) (hb : d81911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2156 q = 1) (hb : d53435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2156, d53435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro291 q ha hb
    | true =>
      simp only [d2156, d53435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2157 q = 1) (hb : d53436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2157, d53436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2157, d53436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81907 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6581 q = 1) (hb : d81908 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6581, d81908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6581, d81908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6582 q = 1) (hb : d81909 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6582, d81909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6582, d81909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6583 q = 1) (hb : d81910 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6583, d81910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6583, d81910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6584 q = 1) (hb : d81911 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6584, d81911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6584, d81911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro9014 (p : Pattern) (ha : d77555 p = 1) (hb : d81921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53408 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53409 q = 1) (hb : d77546 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53409, d77546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9011 q hb ha
    | true =>
      simp only [d53409, d77546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d53410 q = 1) (hb : d77547 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53410, d77547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53410, d77547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53411 q = 1) (hb : d77548 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53411, d77548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53411, d77548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53412 q = 1) (hb : d77549 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53412, d77549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53412, d77549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53418 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53419 q = 1) (hb : d77550 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53419, d77550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9012 q hb ha
    | true =>
      simp only [d53419, d77550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d53420 q = 1) (hb : d77551 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53420, d77551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53420, d77551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53421 q = 1) (hb : d77552 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53421, d77552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53421, d77552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d81915 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d76695 q = 1) (hb : d81916 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76695, d81916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9013 q ha hb
    | true =>
      simp only [d76695, d81916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d76696 q = 1) (hb : d81917 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76696, d81917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76696, d81917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6592 q = 1) (hb : d76312 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d76312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7558 q ha hb
    | true =>
      simp only [d6592, d76312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d6593 q = 1) (hb : d76313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6593, d76313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d6593, d76313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d76697 q = 1) (hb : d81918 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76697, d81918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76697, d81918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77553 q = 1) (hb : d81919 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77553, d81919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d77553, d81919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77554 q = 1) (hb : d81920 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77554, d81920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d77554, d81920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d77555 q = 1) (hb : d81921 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77555, d81921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77555, d81921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro9015 (p : Pattern) (ha : d6598 p = 1) (hb : d53449 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro273 q ha hb
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6547 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6547, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6548 q = 1) (hb : d53379 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6548, d53379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6569 q = 1) (hb : d53405 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6569, d53405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6569, d53405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6598 q = 1) (hb : d53449 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6598, d53449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6598, d53449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro9016 (p : Pattern) (ha : d6603 p = 1) (hb : d53455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d53372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro273 q ha hb
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d53373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6547 q = 1) (hb : d53378 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6547, d53378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6575 q = 1) (hb : d53413 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6575, d53413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6575, d53413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6576 q = 1) (hb : d53414 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6576, d53414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6576, d53414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6603 q = 1) (hb : d53455 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6603, d53455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6603, d53455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro9017 (p : Pattern) (ha : d77565 p = 1) (hb : d81929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53408 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53409 q = 1) (hb : d77546 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53409, d77546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9011 q hb ha
    | true =>
      simp only [d53409, d77546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d53410 q = 1) (hb : d77547 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53410, d77547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53410, d77547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53411 q = 1) (hb : d77548 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53411, d77548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53411, d77548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53412 q = 1) (hb : d77549 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53412, d77549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53412, d77549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53418 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53419 q = 1) (hb : d77550 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53419, d77550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9012 q hb ha
    | true =>
      simp only [d53419, d77550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d53420 q = 1) (hb : d77551 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53420, d77551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53420, d77551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53421 q = 1) (hb : d77552 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53421, d77552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53421, d77552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d81915 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d76695 q = 1) (hb : d81916 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76695, d81916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9013 q ha hb
    | true =>
      simp only [d76695, d81916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d76696 q = 1) (hb : d81917 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76696, d81917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d76696, d81917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6592 q = 1) (hb : d76312 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d76312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7558 q ha hb
    | true =>
      simp only [d6592, d76312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d6593 q = 1) (hb : d76313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6593, d76313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d6593, d76313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d76697 q = 1) (hb : d81918 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76697, d81918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d76697, d81918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77553 q = 1) (hb : d81919 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77553, d81919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d77553, d81919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77554 q = 1) (hb : d81920 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77554, d81920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d77554, d81920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d53450 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d53451 q = 1) (hb : d77556 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53451, d77556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9015 q hb ha
    | true =>
      simp only [d53451, d77556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d53452 q = 1) (hb : d77557 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53452, d77557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53452, d77557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d53453 q = 1) (hb : d77558 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53453, d77558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d53453, d77558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d53454 q = 1) (hb : d77559 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53454, d77559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53454, d77559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d53456 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d53457 q = 1) (hb : d77560 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53457, d77560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9016 q hb ha
    | true =>
      simp only [d53457, d77560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d53458 q = 1) (hb : d77561 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53458, d77561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53458, d77561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d53459 q = 1) (hb : d77562 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53459, d77562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d53459, d77562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d81923 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d76701 q = 1) (hb : d81924 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d76701, d81924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9007 q ha hb
    | true =>
      simp only [d76701, d81924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d0 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    exact ha
  have h31 (q : Pattern) (ha : d76702 q = 1) (hb : d81925 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d76702, d81925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d76702, d81925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d6613 q = 1) (hb : d76331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d76331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7561 q ha hb
    | true =>
      simp only [d6613, d76331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h33 (q : Pattern) (ha : d6614 q = 1) (hb : d76332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6614, d76332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
    | true =>
      simp only [d6614, d76332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h34 (q : Pattern) (ha : d76703 q = 1) (hb : d81926 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d76703, d81926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
    | true =>
      simp only [d76703, d81926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d77563 q = 1) (hb : d81927 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77563, d81927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
    | true =>
      simp only [d77563, d81927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  have h36 (q : Pattern) (ha : d77564 q = 1) (hb : d81928 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77564, d81928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d77564, d81928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h35 q ha hb
  have h37 (q : Pattern) (ha : d77565 q = 1) (hb : d81929 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77565, d81929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d77565, d81929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h36 q ha hb
  exact h37 p ha hb
theorem andIntro9018 (p : Pattern) (ha : d77578 p = 1) (hb : d81973 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53392 q = 1) (hb : d77536 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53392, d77536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53392, d77536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9004 q ha hb
  have h2 (q : Pattern) (ha : d53393 q = 1) (hb : d77537 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53393, d77537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53393, d77537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53402 q = 1) (hb : d77543 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53402, d77543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9004 q ha hb
    | true =>
      simp only [d53402, d77543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9006 q ha hb
  have h4 (q : Pattern) (ha : d53403 q = 1) (hb : d77544 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53403, d77544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53403, d77544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53404 q = 1) (hb : d77545 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53404, d77545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53404, d77545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77566 q = 1) (hb : d81930 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77566, d81930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9014 q ha hb
    | true =>
      simp only [d77566, d81930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9017 q ha hb
  have h7 (q : Pattern) (ha : d5271 q = 1) (hb : d81937 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d5271, d81937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9002 q ha hb
    | true =>
      simp only [d5271, d81937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro282 q ha hb
  have h8 (q : Pattern) (ha : d77567 q = 1) (hb : d81938 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77567, d81938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77567, d81938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77568 q = 1) (hb : d81939 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77568, d81939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d77568, d81939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d77569 q = 1) (hb : d81940 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77569, d81940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d77569, d81940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76712 q = 1) (hb : d81944 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76712, d81944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76712, d81944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9008 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, d53491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, d53491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro283 q ha hb
  have h13 (q : Pattern) (ha : d77570 q = 1) (hb : d81945 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77570, d81945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77570, d81945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d77571 q = 1) (hb : d81946 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77571, d81946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77571, d81946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d77572 q = 1) (hb : d81947 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77572, d81947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d77572, d81947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d77573 q = 1) (hb : d81948 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77573, d81948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77573, d81948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76723 q = 1) (hb : d81968 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d76723, d81968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d76723, d81968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9010 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, d53577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, d53577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro288 q ha hb
  have h19 (q : Pattern) (ha : d77574 q = 1) (hb : d81969 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77574, d81969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77574, d81969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d77575 q = 1) (hb : d81970 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77575, d81970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d77575, d81970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d77576 q = 1) (hb : d81971 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77576, d81971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d77576, d81971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d77577 q = 1) (hb : d81972 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77577, d81972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d77577, d81972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d77578 q = 1) (hb : d81973 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77578, d81973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77578, d81973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro9019 (p : Pattern) (ha : d77584 p = 1) (hb : d81979 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77579 q = 1) (hb : d81974 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77579, d81974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77579, d81974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9018 q ha hb
  have h2 (q : Pattern) (ha : d77580 q = 1) (hb : d81975 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77580, d81975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77580, d81975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77581 q = 1) (hb : d81976 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77581, d81976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77581, d81976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77582 q = 1) (hb : d81977 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77582, d81977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77582, d81977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77583 q = 1) (hb : d81978 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77583, d81978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77583, d81978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77584 q = 1) (hb : d81979 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77584, d81979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77584, d81979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9020 (p : Pattern) (ha : d77590 p = 1) (hb : d81985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d77359 q = 1) (hb : d81662 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77359, d81662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8924 q ha hb
    | true =>
      simp only [d77359, d81662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8943 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d77414 q = 1) (hb : d81740 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77414, d81740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77414, d81740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8962 q ha hb
  have h3 (q : Pattern) (ha : d77415 q = 1) (hb : d81741 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77415, d81741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77415, d81741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77470 q = 1) (hb : d81819 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77470, d81819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77470, d81819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8981 q ha hb
  have h5 (q : Pattern) (ha : d77471 q = 1) (hb : d81820 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77471, d81820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77471, d81820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77472 q = 1) (hb : d81821 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77472, d81821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77472, d81821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77527 q = 1) (hb : d81899 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77527, d81899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77527, d81899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9000 q ha hb
  have h8 (q : Pattern) (ha : d77528 q = 1) (hb : d81900 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77528, d81900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77528, d81900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77529 q = 1) (hb : d81901 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77529, d81901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77529, d81901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77530 q = 1) (hb : d81902 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d77530, d81902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77530, d81902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77585 q = 1) (hb : d81980 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77585, d81980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77585, d81980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9019 q ha hb
  have h12 (q : Pattern) (ha : d77586 q = 1) (hb : d81981 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77586, d81981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77586, d81981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77587 q = 1) (hb : d81982 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77587, d81982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77587, d81982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d77588 q = 1) (hb : d81983 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d77588, d81983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77588, d81983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77589 q = 1) (hb : d81984 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d77589, d81984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77589, d81984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77590 q = 1) (hb : d81985 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d77590, d81985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77590, d81985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro9021 (p : Pattern) (ha : d77596 p = 1) (hb : d81991 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77591 q = 1) (hb : d81986 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d77591, d81986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9020 q ha hb
    | true =>
      simp only [d77591, d81986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77592 q = 1) (hb : d81987 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d77592, d81987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77592, d81987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77593 q = 1) (hb : d81988 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d77593, d81988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77593, d81988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77594 q = 1) (hb : d81989 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d77594, d81989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77594, d81989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77595 q = 1) (hb : d81990 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d77595, d81990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77595, d81990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77596 q = 1) (hb : d81991 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d77596, d81991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77596, d81991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9022 (p : Pattern) (ha : d77602 p = 1) (hb : d81997 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77597 q = 1) (hb : d81992 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d77597, d81992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9021 q ha hb
    | true =>
      simp only [d77597, d81992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77598 q = 1) (hb : d81993 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d77598, d81993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77598, d81993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77599 q = 1) (hb : d81994 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d77599, d81994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77599, d81994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77600 q = 1) (hb : d81995 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d77600, d81995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77600, d81995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77601 q = 1) (hb : d81996 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d77601, d81996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77601, d81996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77602 q = 1) (hb : d81997 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d77602, d81997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77602, d81997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9023 (p : Pattern) (ha : d77608 p = 1) (hb : d82003 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77603 q = 1) (hb : d81998 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d77603, d81998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9022 q ha hb
    | true =>
      simp only [d77603, d81998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77604 q = 1) (hb : d81999 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d77604, d81999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77604, d81999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77605 q = 1) (hb : d82000 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d77605, d82000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77605, d82000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77606 q = 1) (hb : d82001 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d77606, d82001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77606, d82001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77607 q = 1) (hb : d82002 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d77607, d82002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77607, d82002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77608 q = 1) (hb : d82003 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d77608, d82003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77608, d82003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9024 (p : Pattern) (ha : d77614 p = 1) (hb : d82009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77609 q = 1) (hb : d82004 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d77609, d82004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9023 q ha hb
    | true =>
      simp only [d77609, d82004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77610 q = 1) (hb : d82005 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d77610, d82005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77610, d82005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77611 q = 1) (hb : d82006 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d77611, d82006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77611, d82006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77612 q = 1) (hb : d82007 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d77612, d82007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77612, d82007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77613 q = 1) (hb : d82008 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d77613, d82008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77613, d82008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77614 q = 1) (hb : d82009 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d77614, d82009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77614, d82009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9025 (p : Pattern) (ha : d77620 p = 1) (hb : d82015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77615 q = 1) (hb : d82010 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d77615, d82010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9024 q ha hb
    | true =>
      simp only [d77615, d82010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77616 q = 1) (hb : d82011 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d77616, d82011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77616, d82011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77617 q = 1) (hb : d82012 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d77617, d82012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77617, d82012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77618 q = 1) (hb : d82013 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d77618, d82013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77618, d82013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77619 q = 1) (hb : d82014 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d77619, d82014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77619, d82014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77620 q = 1) (hb : d82015 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d77620, d82015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77620, d82015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9026 (p : Pattern) (ha : d77626 p = 1) (hb : d82021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77621 q = 1) (hb : d82016 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d77621, d82016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9025 q ha hb
    | true =>
      simp only [d77621, d82016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77622 q = 1) (hb : d82017 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d77622, d82017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77622, d82017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77623 q = 1) (hb : d82018 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d77623, d82018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77623, d82018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77624 q = 1) (hb : d82019 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d77624, d82019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77624, d82019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77625 q = 1) (hb : d82020 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d77625, d82020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77625, d82020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77626 q = 1) (hb : d82021 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d77626, d82021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77626, d82021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9027 (p : Pattern) (ha : d77632 p = 1) (hb : d82027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77627 q = 1) (hb : d82022 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d77627, d82022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9026 q ha hb
    | true =>
      simp only [d77627, d82022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77628 q = 1) (hb : d82023 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d77628, d82023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77628, d82023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77629 q = 1) (hb : d82024 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d77629, d82024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77629, d82024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77630 q = 1) (hb : d82025 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d77630, d82025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77630, d82025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77631 q = 1) (hb : d82026 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d77631, d82026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77631, d82026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77632 q = 1) (hb : d82027 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d77632, d82027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77632, d82027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9028 (p : Pattern) (ha : d69955 p = 1) (hb : d81525 p = 1) : d77828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75629 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69950 q = 1) (hb : d75629 q = 1) : d77823 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d69950, d77823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8031 q ha hb
    | true =>
      simp only [d69950, d77823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69951 q = 1) (hb : d75629 q = 1) : d77824 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d69951, d77824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69951, d77824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d69952 q = 1) (hb : d81525 q = 1) : d77825 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d69952, d81525, d77825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69952, d81525, d77825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d81525 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69953 q = 1) (hb : d81525 q = 1) : d77826 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d69953, d77826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69953, d77826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69954 q = 1) (hb : d81525 q = 1) : d77827 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d69954, d77827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69954, d77827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d69955 q = 1) (hb : d81525 q = 1) : d77828 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d69955, d77828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69955, d77828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro9029 (p : Pattern) (ha : d69961 p = 1) (hb : d81525 p = 1) : d77834 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d81525 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69956 q = 1) (hb : d81525 q = 1) : d77829 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d69956, d77829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9028 q ha hb
    | true =>
      simp only [d69956, d77829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69957 q = 1) (hb : d81525 q = 1) : d77830 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d69957, d77830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69957, d77830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69958 q = 1) (hb : d81525 q = 1) : d77831 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d69958, d77831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69958, d77831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69959 q = 1) (hb : d81525 q = 1) : d77832 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d69959, d77832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69959, d77832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69960 q = 1) (hb : d81525 q = 1) : d77833 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d69960, d77833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69960, d77833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69961 q = 1) (hb : d81525 q = 1) : d77834 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d69961, d77834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69961, d77834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9030 (p : Pattern) (ha : d69967 p = 1) (hb : d81525 p = 1) : d77840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d81525 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d69962 q = 1) (hb : d81525 q = 1) : d77835 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d69962, d77835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9029 q ha hb
    | true =>
      simp only [d69962, d77835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d69963 q = 1) (hb : d81525 q = 1) : d77836 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d69963, d77836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d69963, d77836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d69964 q = 1) (hb : d81525 q = 1) : d77837 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d69964, d77837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d69964, d77837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d69965 q = 1) (hb : d81525 q = 1) : d77838 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d69965, d77838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d69965, d77838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d69966 q = 1) (hb : d81525 q = 1) : d77839 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d69966, d77839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69966, d77839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69967 q = 1) (hb : d81525 q = 1) : d77840 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d69967, d77840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69967, d77840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9031 (p : Pattern) (ha : d77255 p = 1) (hb : d81539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81534 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51894 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4737 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8901 q ha hb
    | true =>
      simp only [d4737, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4738 q = 1) (hb : d81535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4738, d81535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4738, d81535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d4739 q = 1) (hb : d81536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4739, d81536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4739, d81536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4740 q = 1) (hb : d81537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4740, d81537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4740, d81537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d4741 q = 1) (hb : d81538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4741, d81538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4741, d81538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77255 q = 1) (hb : d81539 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77255, d81539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77255, d81539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro9032 (p : Pattern) (ha : d77262 p = 1) (hb : d81546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81534 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51894 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4737 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8901 q ha hb
    | true =>
      simp only [d4737, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4738 q = 1) (hb : d81535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4738, d81535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4738, d81535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4739 q = 1) (hb : d81536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4739, d81536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4739, d81536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4740 q = 1) (hb : d81537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4740, d81537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4740, d81537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4741 q = 1) (hb : d81538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4741, d81538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4741, d81538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d81541 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d51901 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d5356 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8903 q ha hb
    | true =>
      simp only [d5356, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77258 q = 1) (hb : d81542 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77258, d81542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77258, d81542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d77259 q = 1) (hb : d81543 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77259, d81543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77259, d81543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77260 q = 1) (hb : d81544 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77260, d81544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77260, d81544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d77261 q = 1) (hb : d81545 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77261, d81545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77261, d81545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d77262 q = 1) (hb : d81546 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77262, d81546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77262, d81546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro9033 (p : Pattern) (ha : d77635 p = 1) (hb : d81553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81541 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51901 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5356 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8903 q ha hb
    | true =>
      simp only [d5356, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77258 q = 1) (hb : d81542 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77258, d81542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77258, d81542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d77259 q = 1) (hb : d81543 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77259, d81543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77259, d81543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77260 q = 1) (hb : d81551 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77260, d81551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77260, d81551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77261 q = 1) (hb : d81552 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77261, d81552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77261, d81552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77635 q = 1) (hb : d81553 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77635, d81553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77635, d81553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro9034 (p : Pattern) (ha : d77645 p = 1) (hb : d81572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81567 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51935 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8906 q ha hb
    | true =>
      simp only [d5378, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77641 q = 1) (hb : d81568 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77641, d81568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77641, d81568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74105 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d77642 q = 1) (hb : d81569 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77642, d81569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77642, d81569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77643 q = 1) (hb : d81570 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77643, d81570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77643, d81570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77644 q = 1) (hb : d81571 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77644, d81571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77644, d81571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77645 q = 1) (hb : d81572 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77645, d81572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77645, d81572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro9035 (p : Pattern) (ha : d77651 p = 1) (hb : d81578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77263 q = 1) (hb : d81547 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77263, d81547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9031 q ha hb
    | true =>
      simp only [d77263, d81547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9032 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77264 q = 1) (hb : d81548 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77264, d81548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77264, d81548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77633 q = 1) (hb : d81549 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77633, d81549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77633, d81549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77634 q = 1) (hb : d81550 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77634, d81550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77634, d81550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77636 q = 1) (hb : d81554 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77636, d81554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77636, d81554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9033 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d77637 q = 1) (hb : d81555 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77637, d81555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77637, d81555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77638 q = 1) (hb : d81556 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77638, d81556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77638, d81556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d77639 q = 1) (hb : d81557 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77639, d81557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77639, d81557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d77640 q = 1) (hb : d81558 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77640, d81558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77640, d81558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77646 q = 1) (hb : d81573 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77646, d81573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77646, d81573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9034 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77647 q = 1) (hb : d81574 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77647, d81574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77647, d81574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77648 q = 1) (hb : d81575 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77648, d81575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77648, d81575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d77649 q = 1) (hb : d81576 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77649, d81576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77649, d81576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d77650 q = 1) (hb : d81577 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77650, d81577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77650, d81577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d77651 q = 1) (hb : d81578 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77651, d81578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77651, d81578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro9036 (p : Pattern) (ha : d77657 p = 1) (hb : d81584 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d77652 q = 1) (hb : d81579 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77652, d81579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77652, d81579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9035 q ha hb
  have h8 (q : Pattern) (ha : d77653 q = 1) (hb : d81580 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77653, d81580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77653, d81580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77654 q = 1) (hb : d81581 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77654, d81581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77654, d81581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77655 q = 1) (hb : d81582 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77655, d81582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77655, d81582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77656 q = 1) (hb : d81583 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77656, d81583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77656, d81583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d77657 q = 1) (hb : d81584 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77657, d81584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d77657, d81584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro9037 (p : Pattern) (ha : d77309 p = 1) (hb : d81603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81598 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52238 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5400 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8927 q ha hb
    | true =>
      simp only [d5400, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77305 q = 1) (hb : d81599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77305, d81599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77305, d81599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d77306 q = 1) (hb : d81600 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77306, d81600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77306, d81600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77307 q = 1) (hb : d81601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77307, d81601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77307, d81601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77308 q = 1) (hb : d81602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77308, d81602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77308, d81602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77309 q = 1) (hb : d81603 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77309, d81603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77309, d81603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro9038 (p : Pattern) (ha : d77316 p = 1) (hb : d81611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81598 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52238 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5400 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8927 q ha hb
    | true =>
      simp only [d5400, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77305 q = 1) (hb : d81599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77305, d81599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77305, d81599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74127 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d77306 q = 1) (hb : d81600 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77306, d81600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77306, d81600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77307 q = 1) (hb : d81601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77307, d81601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77307, d81601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77308 q = 1) (hb : d81602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77308, d81602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77308, d81602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52321 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52326 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d81606 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52248 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d5407 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8929 q ha hb
    | true =>
      simp only [d5407, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77312 q = 1) (hb : d81607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77312, d81607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77312, d81607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d77313 q = 1) (hb : d81608 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77313, d81608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77313, d81608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77314 q = 1) (hb : d81609 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77314, d81609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77314, d81609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d77315 q = 1) (hb : d81610 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77315, d81610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77315, d81610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d77316 q = 1) (hb : d81611 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77316, d81611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77316, d81611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro9039 (p : Pattern) (ha : d77660 p = 1) (hb : d81625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81606 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52248 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5407 q = 1) (hb : d52249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8929 q ha hb
    | true =>
      simp only [d5407, d52249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77312 q = 1) (hb : d81607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77312, d81607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77312, d81607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74134 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d77313 q = 1) (hb : d81608 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77313, d81608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77313, d81608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77314 q = 1) (hb : d81623 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77314, d81623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77314, d81623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77315 q = 1) (hb : d81624 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77315, d81624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77315, d81624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77660 q = 1) (hb : d81625 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77660, d81625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77660, d81625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro9040 (p : Pattern) (ha : d5428 p = 1) (hb : d52393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d676 q = 1) (hb : d52380 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d676, d52380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro83 q ha hb
    | true =>
      simp only [d676, d52380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d677 q = 1) (hb : d52381 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d677, d52381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d677, d52381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5425 q = 1) (hb : d52390 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5425, d52390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5425, d52390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5426 q = 1) (hb : d52391 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5426, d52391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5426, d52391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5427 q = 1) (hb : d52392 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5427, d52392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5427, d52392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d5428 q = 1) (hb : d52393 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5428, d52393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5428, d52393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro9041 (p : Pattern) (ha : d77670 p = 1) (hb : d81649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81644 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5429 q = 1) (hb : d52399 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5429, d52399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9040 q ha hb
    | true =>
      simp only [d5429, d52399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77666 q = 1) (hb : d81645 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77666, d81645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77666, d81645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74156 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d77667 q = 1) (hb : d81646 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77667, d81646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77667, d81646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77668 q = 1) (hb : d81647 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77668, d81647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77668, d81647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77669 q = 1) (hb : d81648 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77669, d81648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77669, d81648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77670 q = 1) (hb : d81649 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77670, d81649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77670, d81649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro9042 (p : Pattern) (ha : d77676 p = 1) (hb : d81655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77317 q = 1) (hb : d81612 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77317, d81612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9037 q ha hb
    | true =>
      simp only [d77317, d81612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9038 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81619 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77318 q = 1) (hb : d81620 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77318, d81620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77318, d81620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77658 q = 1) (hb : d81621 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77658, d81621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77658, d81621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77659 q = 1) (hb : d81622 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77659, d81622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77659, d81622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77661 q = 1) (hb : d81626 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77661, d81626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77661, d81626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9039 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d77662 q = 1) (hb : d81627 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77662, d81627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77662, d81627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77663 q = 1) (hb : d81628 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77663, d81628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77663, d81628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d77664 q = 1) (hb : d81629 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77664, d81629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77664, d81629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d77665 q = 1) (hb : d81630 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77665, d81630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77665, d81630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77671 q = 1) (hb : d81650 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77671, d81650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77671, d81650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9041 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77672 q = 1) (hb : d81651 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77672, d81651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77672, d81651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77673 q = 1) (hb : d81652 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77673, d81652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77673, d81652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d77674 q = 1) (hb : d81653 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77674, d81653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77674, d81653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d77675 q = 1) (hb : d81654 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77675, d81654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77675, d81654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d77676 q = 1) (hb : d81655 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77676, d81655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77676, d81655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro9043 (p : Pattern) (ha : d77682 p = 1) (hb : d81661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77677 q = 1) (hb : d81656 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77677, d81656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77677, d81656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9042 q ha hb
  have h2 (q : Pattern) (ha : d77678 q = 1) (hb : d81657 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77678, d81657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77678, d81657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77679 q = 1) (hb : d81658 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77679, d81658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77679, d81658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77680 q = 1) (hb : d81659 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77680, d81659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77680, d81659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77681 q = 1) (hb : d81660 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77681, d81660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77681, d81660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77682 q = 1) (hb : d81661 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77682, d81661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77682, d81661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9044 (p : Pattern) (ha : d77364 p = 1) (hb : d81681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81676 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52460 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6160 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6160, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8946 q ha hb
    | true =>
      simp only [d6160, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77360 q = 1) (hb : d81677 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77360, d81677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77360, d81677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d75914 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d77361 q = 1) (hb : d81678 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77361, d81678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77361, d81678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77362 q = 1) (hb : d81679 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77362, d81679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77362, d81679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77363 q = 1) (hb : d81680 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77363, d81680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77363, d81680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77364 q = 1) (hb : d81681 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77364, d81681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77364, d81681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro9045 (p : Pattern) (ha : d77371 p = 1) (hb : d81689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81676 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52460 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6160 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6160, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8946 q ha hb
    | true =>
      simp only [d6160, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77360 q = 1) (hb : d81677 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77360, d81677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77360, d81677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d75914 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d77361 q = 1) (hb : d81678 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77361, d81678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77361, d81678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77362 q = 1) (hb : d81679 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77362, d81679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77362, d81679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77363 q = 1) (hb : d81680 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77363, d81680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77363, d81680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52542 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52547 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d81684 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52470 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d6181 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6181, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8948 q ha hb
    | true =>
      simp only [d6181, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77367 q = 1) (hb : d81685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77367, d81685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77367, d81685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d75933 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d77368 q = 1) (hb : d81686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77368, d81686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77368, d81686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77369 q = 1) (hb : d81687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77369, d81687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77369, d81687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d77370 q = 1) (hb : d81688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77370, d81688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77370, d81688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d77371 q = 1) (hb : d81689 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77371, d81689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77371, d81689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro9046 (p : Pattern) (ha : d77686 p = 1) (hb : d81703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81684 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52470 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6181 q = 1) (hb : d52471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6181, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8948 q ha hb
    | true =>
      simp only [d6181, d52471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77367 q = 1) (hb : d81685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77367, d81685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77367, d81685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d75933 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d77368 q = 1) (hb : d81686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77368, d81686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77368, d81686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77369 q = 1) (hb : d81701 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77369, d81701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77369, d81701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77370 q = 1) (hb : d81702 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77370, d81702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77370, d81702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77686 q = 1) (hb : d81703 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77686, d81703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77686, d81703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro9047 (p : Pattern) (ha : d6233 p = 1) (hb : d52630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d998 q = 1) (hb : d52617 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d998, d52617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro130 q ha hb
    | true =>
      simp only [d998, d52617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d999 q = 1) (hb : d52618 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d999, d52618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d999, d52618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52626 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6230 q = 1) (hb : d52627 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6230, d52627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6230, d52627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6231 q = 1) (hb : d52628 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6231, d52628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6231, d52628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6232 q = 1) (hb : d52629 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6232, d52629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6232, d52629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6233 q = 1) (hb : d52630 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6233, d52630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6233, d52630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro9048 (p : Pattern) (ha : d77696 p = 1) (hb : d81727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81722 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52635 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6234 q = 1) (hb : d52636 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6234, d52636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9047 q ha hb
    | true =>
      simp only [d6234, d52636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77692 q = 1) (hb : d81723 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77692, d81723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77692, d81723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d75982 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d77693 q = 1) (hb : d81724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77693, d81724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77693, d81724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77694 q = 1) (hb : d81725 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77694, d81725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77694, d81725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77695 q = 1) (hb : d81726 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77695, d81726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77695, d81726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77696 q = 1) (hb : d81727 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77696, d81727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77696, d81727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro9049 (p : Pattern) (ha : d77702 p = 1) (hb : d81733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77372 q = 1) (hb : d81690 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77372, d81690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9044 q ha hb
    | true =>
      simp only [d77372, d81690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9045 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81697 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77373 q = 1) (hb : d81698 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77373, d81698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77373, d81698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77684 q = 1) (hb : d81699 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77684, d81699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77684, d81699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77685 q = 1) (hb : d81700 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77685, d81700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77685, d81700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77687 q = 1) (hb : d81704 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77687, d81704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77687, d81704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9046 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d77688 q = 1) (hb : d81705 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77688, d81705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77688, d81705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77689 q = 1) (hb : d81706 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77689, d81706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77689, d81706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d77690 q = 1) (hb : d81707 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77690, d81707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77690, d81707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d77691 q = 1) (hb : d81708 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77691, d81708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77691, d81708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77697 q = 1) (hb : d81728 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77697, d81728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77697, d81728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9048 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77698 q = 1) (hb : d81729 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77698, d81729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77698, d81729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77699 q = 1) (hb : d81730 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77699, d81730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77699, d81730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d77700 q = 1) (hb : d81731 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77700, d81731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77700, d81731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d77701 q = 1) (hb : d81732 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77701, d81732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77701, d81732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d77702 q = 1) (hb : d81733 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77702, d81733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77702, d81733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro9050 (p : Pattern) (ha : d77708 p = 1) (hb : d81739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77703 q = 1) (hb : d81734 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77703, d81734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77703, d81734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9049 q ha hb
  have h2 (q : Pattern) (ha : d77704 q = 1) (hb : d81735 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77704, d81735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77704, d81735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77705 q = 1) (hb : d81736 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77705, d81736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77705, d81736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77706 q = 1) (hb : d81737 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77706, d81737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77706, d81737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77707 q = 1) (hb : d81738 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77707, d81738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77707, d81738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77708 q = 1) (hb : d81739 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77708, d81739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77708, d81739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9051 (p : Pattern) (ha : d77420 p = 1) (hb : d81760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81755 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52743 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6299 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6299, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8965 q ha hb
    | true =>
      simp only [d6299, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77416 q = 1) (hb : d81756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77416, d81756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77416, d81756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d76042 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d77417 q = 1) (hb : d81757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77417, d81757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77417, d81757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77418 q = 1) (hb : d81758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77418, d81758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77418, d81758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77419 q = 1) (hb : d81759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77419, d81759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77419, d81759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77420 q = 1) (hb : d81760 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77420, d81760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77420, d81760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro9052 (p : Pattern) (ha : d77427 p = 1) (hb : d81768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81755 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52743 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6299 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6299, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8965 q ha hb
    | true =>
      simp only [d6299, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77416 q = 1) (hb : d81756 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77416, d81756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77416, d81756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d76042 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d77417 q = 1) (hb : d81757 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77417, d81757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77417, d81757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77418 q = 1) (hb : d81758 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77418, d81758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77418, d81758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77419 q = 1) (hb : d81759 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77419, d81759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77419, d81759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52822 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52827 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d81763 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d52753 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d6320 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6320, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8967 q ha hb
    | true =>
      simp only [d6320, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77423 q = 1) (hb : d81764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77423, d81764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77423, d81764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d76061 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d77424 q = 1) (hb : d81765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77424, d81765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77424, d81765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77425 q = 1) (hb : d81766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77425, d81766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77425, d81766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d77426 q = 1) (hb : d81767 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77426, d81767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77426, d81767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d77427 q = 1) (hb : d81768 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77427, d81768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77427, d81768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro9053 (p : Pattern) (ha : d77713 p = 1) (hb : d81782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81763 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52753 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6320 q = 1) (hb : d52754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6320, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8967 q ha hb
    | true =>
      simp only [d6320, d52754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77423 q = 1) (hb : d81764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77423, d81764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77423, d81764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76061 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d77424 q = 1) (hb : d81765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77424, d81765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77424, d81765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77425 q = 1) (hb : d81780 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77425, d81780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77425, d81780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77426 q = 1) (hb : d81781 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77426, d81781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77426, d81781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77713 q = 1) (hb : d81782 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77713, d81782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77713, d81782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro9054 (p : Pattern) (ha : d6378 p = 1) (hb : d52924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1423 q = 1) (hb : d52911 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1423, d52911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro182 q ha hb
    | true =>
      simp only [d1423, d52911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1424 q = 1) (hb : d52912 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1424, d52912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1424, d52912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52920 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6375 q = 1) (hb : d52921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6375, d52921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6375, d52921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6376 q = 1) (hb : d52922 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6376, d52922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6376, d52922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6377 q = 1) (hb : d52923 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6377, d52923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6377, d52923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6378 q = 1) (hb : d52924 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6378, d52924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6378, d52924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro9055 (p : Pattern) (ha : d77723 p = 1) (hb : d81806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81801 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52929 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6379 q = 1) (hb : d52930 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6379, d52930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9054 q ha hb
    | true =>
      simp only [d6379, d52930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77719 q = 1) (hb : d81802 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77719, d81802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77719, d81802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76116 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d77720 q = 1) (hb : d81803 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77720, d81803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77720, d81803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77721 q = 1) (hb : d81804 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77721, d81804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77721, d81804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77722 q = 1) (hb : d81805 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77722, d81805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77722, d81805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77723 q = 1) (hb : d81806 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77723, d81806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77723, d81806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro9056 (p : Pattern) (ha : d77729 p = 1) (hb : d81812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77428 q = 1) (hb : d81769 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77428, d81769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9051 q ha hb
    | true =>
      simp only [d77428, d81769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9052 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81776 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77429 q = 1) (hb : d81777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77429, d81777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77429, d81777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77711 q = 1) (hb : d81778 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77711, d81778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77711, d81778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77712 q = 1) (hb : d81779 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77712, d81779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77712, d81779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77714 q = 1) (hb : d81783 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77714, d81783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77714, d81783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9053 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d77715 q = 1) (hb : d81784 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77715, d81784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77715, d81784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77716 q = 1) (hb : d81785 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77716, d81785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77716, d81785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d77717 q = 1) (hb : d81786 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77717, d81786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77717, d81786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d77718 q = 1) (hb : d81787 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77718, d81787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77718, d81787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77724 q = 1) (hb : d81807 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77724, d81807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77724, d81807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9055 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77725 q = 1) (hb : d81808 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77725, d81808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77725, d81808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77726 q = 1) (hb : d81809 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77726, d81809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77726, d81809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d77727 q = 1) (hb : d81810 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77727, d81810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77727, d81810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d77728 q = 1) (hb : d81811 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77728, d81811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77728, d81811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d77729 q = 1) (hb : d81812 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77729, d81812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77729, d81812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro9057 (p : Pattern) (ha : d77735 p = 1) (hb : d81818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77730 q = 1) (hb : d81813 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77730, d81813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77730, d81813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9056 q ha hb
  have h2 (q : Pattern) (ha : d77731 q = 1) (hb : d81814 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77731, d81814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77731, d81814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77732 q = 1) (hb : d81815 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77732, d81815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77732, d81815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77733 q = 1) (hb : d81816 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77733, d81816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77733, d81816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77734 q = 1) (hb : d81817 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77734, d81817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77734, d81817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77735 q = 1) (hb : d81818 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77735, d81818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77735, d81818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9058 (p : Pattern) (ha : d77477 p = 1) (hb : d81840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81835 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53064 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6445 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6445, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8984 q ha hb
    | true =>
      simp only [d6445, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77473 q = 1) (hb : d81836 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77473, d81836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77473, d81836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d76177 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d77474 q = 1) (hb : d81837 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77474, d81837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77474, d81837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77475 q = 1) (hb : d81838 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77475, d81838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77475, d81838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77476 q = 1) (hb : d81839 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77476, d81839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77476, d81839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77477 q = 1) (hb : d81840 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77477, d81840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77477, d81840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro9059 (p : Pattern) (ha : d77484 p = 1) (hb : d81848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81835 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53064 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6445 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6445, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8984 q ha hb
    | true =>
      simp only [d6445, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77473 q = 1) (hb : d81836 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77473, d81836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77473, d81836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d76177 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d77474 q = 1) (hb : d81837 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77474, d81837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77474, d81837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77475 q = 1) (hb : d81838 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77475, d81838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77475, d81838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77476 q = 1) (hb : d81839 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77476, d81839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77476, d81839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53137 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53142 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d81843 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d53074 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d6466 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6466, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8986 q ha hb
    | true =>
      simp only [d6466, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77480 q = 1) (hb : d81844 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77480, d81844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77480, d81844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d76196 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d77481 q = 1) (hb : d81845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77481, d81845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77481, d81845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77482 q = 1) (hb : d81846 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77482, d81846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77482, d81846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d77483 q = 1) (hb : d81847 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77483, d81847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77483, d81847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d77484 q = 1) (hb : d81848 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77484, d81848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77484, d81848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro9060 (p : Pattern) (ha : d77741 p = 1) (hb : d81862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81843 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53074 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6466 q = 1) (hb : d53075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6466, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8986 q ha hb
    | true =>
      simp only [d6466, d53075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77480 q = 1) (hb : d81844 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77480, d81844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77480, d81844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76196 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d77481 q = 1) (hb : d81845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77481, d81845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77481, d81845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77482 q = 1) (hb : d81860 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77482, d81860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77482, d81860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77483 q = 1) (hb : d81861 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77483, d81861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77483, d81861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77741 q = 1) (hb : d81862 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77741, d81862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77741, d81862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro9061 (p : Pattern) (ha : d6524 p = 1) (hb : d53239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1900 q = 1) (hb : d53226 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1900, d53226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro238 q ha hb
    | true =>
      simp only [d1900, d53226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1901 q = 1) (hb : d53227 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1901, d53227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1901, d53227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53235 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6521 q = 1) (hb : d53236 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6521, d53236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6521, d53236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6522 q = 1) (hb : d53237 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6522, d53237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6522, d53237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6523 q = 1) (hb : d53238 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6523, d53238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6523, d53238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6524 q = 1) (hb : d53239 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6524, d53239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6524, d53239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro9062 (p : Pattern) (ha : d77751 p = 1) (hb : d81886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81881 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53244 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6525 q = 1) (hb : d53245 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6525, d53245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9061 q ha hb
    | true =>
      simp only [d6525, d53245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77747 q = 1) (hb : d81882 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77747, d81882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77747, d81882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76251 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d77748 q = 1) (hb : d81883 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77748, d81883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77748, d81883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77749 q = 1) (hb : d81884 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77749, d81884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77749, d81884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77750 q = 1) (hb : d81885 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77750, d81885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77750, d81885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77751 q = 1) (hb : d81886 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77751, d81886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77751, d81886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro9063 (p : Pattern) (ha : d77757 p = 1) (hb : d81892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77485 q = 1) (hb : d81849 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77485, d81849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9058 q ha hb
    | true =>
      simp only [d77485, d81849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9059 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81856 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77486 q = 1) (hb : d81857 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77486, d81857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77486, d81857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77739 q = 1) (hb : d81858 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77739, d81858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77739, d81858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77740 q = 1) (hb : d81859 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77740, d81859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77740, d81859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77742 q = 1) (hb : d81863 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77742, d81863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77742, d81863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9060 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d77743 q = 1) (hb : d81864 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77743, d81864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77743, d81864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77744 q = 1) (hb : d81865 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77744, d81865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77744, d81865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d77745 q = 1) (hb : d81866 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77745, d81866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77745, d81866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d77746 q = 1) (hb : d81867 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77746, d81867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77746, d81867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77752 q = 1) (hb : d81887 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77752, d81887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77752, d81887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9062 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77753 q = 1) (hb : d81888 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77753, d81888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77753, d81888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77754 q = 1) (hb : d81889 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77754, d81889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77754, d81889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d77755 q = 1) (hb : d81890 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77755, d81890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77755, d81890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d77756 q = 1) (hb : d81891 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77756, d81891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77756, d81891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d77757 q = 1) (hb : d81892 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77757, d81892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77757, d81892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro9064 (p : Pattern) (ha : d77763 p = 1) (hb : d81898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77758 q = 1) (hb : d81893 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77758, d81893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77758, d81893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9063 q ha hb
  have h2 (q : Pattern) (ha : d77759 q = 1) (hb : d81894 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77759, d81894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77759, d81894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77760 q = 1) (hb : d81895 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77760, d81895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77760, d81895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77761 q = 1) (hb : d81896 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77761, d81896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77761, d81896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77762 q = 1) (hb : d81897 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77762, d81897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77762, d81897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77763 q = 1) (hb : d81898 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77763, d81898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77763, d81898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9065 (p : Pattern) (ha : d77535 p = 1) (hb : d81921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d81916 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53385 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6592 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9003 q ha hb
    | true =>
      simp only [d6592, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77531 q = 1) (hb : d81917 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77531, d81917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77531, d81917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d76313 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d77532 q = 1) (hb : d81918 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77532, d81918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77532, d81918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77533 q = 1) (hb : d81919 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77533, d81919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77533, d81919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77534 q = 1) (hb : d81920 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77534, d81920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77534, d81920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77535 q = 1) (hb : d81921 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77535, d81921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77535, d81921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro9066 (p : Pattern) (ha : d77542 p = 1) (hb : d81929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81916 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53385 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6592 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9003 q ha hb
    | true =>
      simp only [d6592, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77531 q = 1) (hb : d81917 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77531, d81917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77531, d81917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d76313 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d77532 q = 1) (hb : d81918 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77532, d81918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77532, d81918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77533 q = 1) (hb : d81919 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77533, d81919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77533, d81919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77534 q = 1) (hb : d81920 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77534, d81920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77534, d81920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53454 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53459 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d81924 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d53395 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d6613 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9005 q ha hb
    | true =>
      simp only [d6613, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77538 q = 1) (hb : d81925 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77538, d81925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77538, d81925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d76332 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d77539 q = 1) (hb : d81926 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77539, d81926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77539, d81926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77540 q = 1) (hb : d81927 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77540, d81927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77540, d81927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d77541 q = 1) (hb : d81928 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77541, d81928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77541, d81928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d77542 q = 1) (hb : d81929 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77542, d81929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77542, d81929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro9067 (p : Pattern) (ha : d77770 p = 1) (hb : d81943 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81924 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53395 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6613 q = 1) (hb : d53396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9005 q ha hb
    | true =>
      simp only [d6613, d53396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77538 q = 1) (hb : d81925 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77538, d81925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77538, d81925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76332 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d77539 q = 1) (hb : d81926 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77539, d81926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77539, d81926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77540 q = 1) (hb : d81941 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77540, d81941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77540, d81941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77541 q = 1) (hb : d81942 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77541, d81942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77541, d81942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77770 q = 1) (hb : d81943 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77770, d81943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77770, d81943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro9068 (p : Pattern) (ha : d6671 p = 1) (hb : d53556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2378 q = 1) (hb : d53543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2378, d53543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro297 q ha hb
    | true =>
      simp only [d2378, d53543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2379 q = 1) (hb : d53544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2379, d53544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2379, d53544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53552 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6668 q = 1) (hb : d53553 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6668, d53553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6668, d53553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6669 q = 1) (hb : d53554 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6669, d53554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6669, d53554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d6670 q = 1) (hb : d53555 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6670, d53555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6670, d53555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6671 q = 1) (hb : d53556 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6671, d53556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6671, d53556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro9069 (p : Pattern) (ha : d77780 p = 1) (hb : d81967 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d81962 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53561 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d6672 q = 1) (hb : d53562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6672, d53562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9068 q ha hb
    | true =>
      simp only [d6672, d53562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77776 q = 1) (hb : d81963 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77776, d81963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77776, d81963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76387 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d77777 q = 1) (hb : d81964 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77777, d81964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77777, d81964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77778 q = 1) (hb : d81965 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77778, d81965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77778, d81965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77779 q = 1) (hb : d81966 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77779, d81966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77779, d81966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77780 q = 1) (hb : d81967 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77780, d81967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77780, d81967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro9070 (p : Pattern) (ha : d77786 p = 1) (hb : d81973 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77543 q = 1) (hb : d81930 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77543, d81930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9065 q ha hb
    | true =>
      simp only [d77543, d81930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9066 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d81937 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77544 q = 1) (hb : d81938 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77544, d81938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77544, d81938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77768 q = 1) (hb : d81939 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77768, d81939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77768, d81939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77769 q = 1) (hb : d81940 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77769, d81940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77769, d81940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77771 q = 1) (hb : d81944 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77771, d81944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77771, d81944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9067 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d77772 q = 1) (hb : d81945 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77772, d81945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77772, d81945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77773 q = 1) (hb : d81946 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77773, d81946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77773, d81946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d77774 q = 1) (hb : d81947 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77774, d81947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77774, d81947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d77775 q = 1) (hb : d81948 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77775, d81948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77775, d81948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77781 q = 1) (hb : d81968 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77781, d81968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77781, d81968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9069 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77782 q = 1) (hb : d81969 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77782, d81969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77782, d81969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77783 q = 1) (hb : d81970 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77783, d81970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77783, d81970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d77784 q = 1) (hb : d81971 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77784, d81971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77784, d81971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d77785 q = 1) (hb : d81972 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77785, d81972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77785, d81972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d77786 q = 1) (hb : d81973 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77786, d81973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77786, d81973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro9071 (p : Pattern) (ha : d77792 p = 1) (hb : d81979 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77787 q = 1) (hb : d81974 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77787, d81974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77787, d81974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9070 q ha hb
  have h2 (q : Pattern) (ha : d77788 q = 1) (hb : d81975 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77788, d81975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77788, d81975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77789 q = 1) (hb : d81976 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77789, d81976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77789, d81976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77790 q = 1) (hb : d81977 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77790, d81977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77790, d81977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77791 q = 1) (hb : d81978 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77791, d81978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77791, d81978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77792 q = 1) (hb : d81979 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77792, d81979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77792, d81979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9072 (p : Pattern) (ha : d77798 p = 1) (hb : d81985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d77683 q = 1) (hb : d81662 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77683, d81662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9036 q ha hb
    | true =>
      simp only [d77683, d81662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9043 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d77709 q = 1) (hb : d81740 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77709, d81740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77709, d81740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9050 q ha hb
  have h3 (q : Pattern) (ha : d77710 q = 1) (hb : d81741 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77710, d81741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77710, d81741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77736 q = 1) (hb : d81819 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77736, d81819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77736, d81819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9057 q ha hb
  have h5 (q : Pattern) (ha : d77737 q = 1) (hb : d81820 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77737, d81820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77737, d81820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77738 q = 1) (hb : d81821 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77738, d81821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77738, d81821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77764 q = 1) (hb : d81899 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77764, d81899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77764, d81899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9064 q ha hb
  have h8 (q : Pattern) (ha : d77765 q = 1) (hb : d81900 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77765, d81900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77765, d81900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77766 q = 1) (hb : d81901 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77766, d81901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77766, d81901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77767 q = 1) (hb : d81902 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d77767, d81902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77767, d81902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77793 q = 1) (hb : d81980 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77793, d81980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77793, d81980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9071 q ha hb
  have h12 (q : Pattern) (ha : d77794 q = 1) (hb : d81981 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77794, d81981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77794, d81981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77795 q = 1) (hb : d81982 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77795, d81982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77795, d81982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d77796 q = 1) (hb : d81983 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d77796, d81983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77796, d81983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77797 q = 1) (hb : d81984 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d77797, d81984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77797, d81984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77798 q = 1) (hb : d81985 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d77798, d81985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77798, d81985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro9073 (p : Pattern) (ha : d77804 p = 1) (hb : d81991 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77799 q = 1) (hb : d81986 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d77799, d81986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9072 q ha hb
    | true =>
      simp only [d77799, d81986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77800 q = 1) (hb : d81987 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d77800, d81987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77800, d81987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77801 q = 1) (hb : d81988 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d77801, d81988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77801, d81988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77802 q = 1) (hb : d81989 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d77802, d81989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77802, d81989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77803 q = 1) (hb : d81990 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d77803, d81990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77803, d81990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77804 q = 1) (hb : d81991 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d77804, d81991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77804, d81991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9074 (p : Pattern) (ha : d77810 p = 1) (hb : d81997 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77805 q = 1) (hb : d81992 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d77805, d81992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9073 q ha hb
    | true =>
      simp only [d77805, d81992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77806 q = 1) (hb : d81993 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d77806, d81993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77806, d81993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77807 q = 1) (hb : d81994 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d77807, d81994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77807, d81994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77808 q = 1) (hb : d81995 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d77808, d81995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77808, d81995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77809 q = 1) (hb : d81996 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d77809, d81996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77809, d81996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77810 q = 1) (hb : d81997 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d77810, d81997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77810, d81997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9075 (p : Pattern) (ha : d77816 p = 1) (hb : d82003 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77811 q = 1) (hb : d81998 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d77811, d81998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9074 q ha hb
    | true =>
      simp only [d77811, d81998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77812 q = 1) (hb : d81999 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d77812, d81999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77812, d81999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77813 q = 1) (hb : d82000 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d77813, d82000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77813, d82000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77814 q = 1) (hb : d82001 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d77814, d82001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77814, d82001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77815 q = 1) (hb : d82002 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d77815, d82002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77815, d82002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77816 q = 1) (hb : d82003 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d77816, d82003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77816, d82003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9076 (p : Pattern) (ha : d77822 p = 1) (hb : d82009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77817 q = 1) (hb : d82004 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d77817, d82004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9075 q ha hb
    | true =>
      simp only [d77817, d82004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77818 q = 1) (hb : d82005 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d77818, d82005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77818, d82005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77819 q = 1) (hb : d82006 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d77819, d82006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77819, d82006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77820 q = 1) (hb : d82007 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d77820, d82007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77820, d82007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77821 q = 1) (hb : d82008 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d77821, d82008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77821, d82008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77822 q = 1) (hb : d82009 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d77822, d82009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77822, d82009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9077 (p : Pattern) (ha : d77828 p = 1) (hb : d82015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77823 q = 1) (hb : d82010 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d77823, d82010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9076 q ha hb
    | true =>
      simp only [d77823, d82010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77824 q = 1) (hb : d82011 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d77824, d82011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77824, d82011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77825 q = 1) (hb : d82012 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d77825, d82012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77825, d82012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77826 q = 1) (hb : d82013 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d77826, d82013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77826, d82013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77827 q = 1) (hb : d82014 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d77827, d82014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77827, d82014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77828 q = 1) (hb : d82015 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d77828, d82015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77828, d82015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9078 (p : Pattern) (ha : d77834 p = 1) (hb : d82021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77829 q = 1) (hb : d82016 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d77829, d82016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9077 q ha hb
    | true =>
      simp only [d77829, d82016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77830 q = 1) (hb : d82017 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d77830, d82017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77830, d82017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77831 q = 1) (hb : d82018 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d77831, d82018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77831, d82018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77832 q = 1) (hb : d82019 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d77832, d82019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77832, d82019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77833 q = 1) (hb : d82020 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d77833, d82020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77833, d82020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77834 q = 1) (hb : d82021 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d77834, d82021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77834, d82021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9079 (p : Pattern) (ha : d77840 p = 1) (hb : d82027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77835 q = 1) (hb : d82022 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d77835, d82022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9078 q ha hb
    | true =>
      simp only [d77835, d82022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77836 q = 1) (hb : d82023 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d77836, d82023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77836, d82023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77837 q = 1) (hb : d82024 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d77837, d82024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77837, d82024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77838 q = 1) (hb : d82025 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d77838, d82025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77838, d82025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77839 q = 1) (hb : d82026 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d77839, d82026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77839, d82026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77840 q = 1) (hb : d82027 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d77840, d82027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77840, d82027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9080 (p : Pattern) (ha : d77255 p = 1) (hb : d82032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6746 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d4737 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4738 q = 1) (hb : d82028 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4738, d82028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4738, d82028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4739 q = 1) (hb : d82029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4739, d82029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4739, d82029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4740 q = 1) (hb : d82030 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4740, d82030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4740, d82030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4741 q = 1) (hb : d82031 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4741, d82031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4741, d82031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77255 q = 1) (hb : d82032 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77255, d82032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77255, d82032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro9081 (p : Pattern) (ha : d77262 p = 1) (hb : d82037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6746 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d4737 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4738 q = 1) (hb : d82028 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4738, d82028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4738, d82028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4739 q = 1) (hb : d82029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4739, d82029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4739, d82029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4740 q = 1) (hb : d82030 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4740, d82030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4740, d82030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4741 q = 1) (hb : d82031 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4741, d82031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4741, d82031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d380 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d384 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6753 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d5356 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d77258 q = 1) (hb : d82033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77258, d82033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77258, d82033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77259 q = 1) (hb : d82034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77259, d82034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77259, d82034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77260 q = 1) (hb : d82035 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77260, d82035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77260, d82035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77261 q = 1) (hb : d82036 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77261, d82036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77261, d82036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77262 q = 1) (hb : d82037 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77262, d82037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d77262, d82037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro9082 (p : Pattern) (ha : d77635 p = 1) (hb : d82044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5356 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77258 q = 1) (hb : d82033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77258, d82033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77258, d82033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77259 q = 1) (hb : d82034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77259, d82034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77259, d82034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77260 q = 1) (hb : d82042 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77260, d82042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77260, d82042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77261 q = 1) (hb : d82043 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77261, d82043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77261, d82043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77635 q = 1) (hb : d82044 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77635, d82044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77635, d82044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9083 (p : Pattern) (ha : d77645 p = 1) (hb : d82054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5378 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77641 q = 1) (hb : d82050 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77641, d82050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77641, d82050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5379 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77642 q = 1) (hb : d82051 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77642, d82051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77642, d82051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77643 q = 1) (hb : d82052 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77643, d82052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77643, d82052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77644 q = 1) (hb : d82053 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77644, d82053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77644, d82053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77645 q = 1) (hb : d82054 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77645, d82054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77645, d82054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9084 (p : Pattern) (ha : d77651 p = 1) (hb : d82060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77263 q = 1) (hb : d82038 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77263, d82038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9080 q ha hb
    | true =>
      simp only [d77263, d82038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9081 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77264 q = 1) (hb : d82039 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77264, d82039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77264, d82039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77633 q = 1) (hb : d82040 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77633, d82040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77633, d82040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77634 q = 1) (hb : d82041 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77634, d82041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77634, d82041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77636 q = 1) (hb : d82045 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77636, d82045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77636, d82045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9082 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d77637 q = 1) (hb : d82046 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77637, d82046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77637, d82046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77638 q = 1) (hb : d82047 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77638, d82047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77638, d82047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d77639 q = 1) (hb : d82048 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77639, d82048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77639, d82048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d77640 q = 1) (hb : d82049 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77640, d82049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77640, d82049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77646 q = 1) (hb : d82055 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77646, d82055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77646, d82055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9083 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77647 q = 1) (hb : d82056 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77647, d82056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77647, d82056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77648 q = 1) (hb : d82057 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77648, d82057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77648, d82057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d77649 q = 1) (hb : d82058 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77649, d82058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77649, d82058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d77650 q = 1) (hb : d82059 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77650, d82059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77650, d82059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d77651 q = 1) (hb : d82060 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77651, d82060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77651, d82060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro9085 (p : Pattern) (ha : d77657 p = 1) (hb : d82066 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d77652 q = 1) (hb : d82061 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77652, d82061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77652, d82061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9084 q ha hb
  have h8 (q : Pattern) (ha : d77653 q = 1) (hb : d82062 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77653, d82062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77653, d82062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77654 q = 1) (hb : d82063 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77654, d82063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77654, d82063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77655 q = 1) (hb : d82064 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77655, d82064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77655, d82064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77656 q = 1) (hb : d82065 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77656, d82065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77656, d82065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d77657 q = 1) (hb : d82066 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77657, d82066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d77657, d82066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro9086 (p : Pattern) (ha : d77309 p = 1) (hb : d82071 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d518 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d527 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6810 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5400 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77305 q = 1) (hb : d82067 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77305, d82067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77305, d82067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5401 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d77306 q = 1) (hb : d82068 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77306, d82068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77306, d82068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77307 q = 1) (hb : d82069 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77307, d82069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77307, d82069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77308 q = 1) (hb : d82070 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77308, d82070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77308, d82070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77309 q = 1) (hb : d82071 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77309, d82071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77309, d82071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro9087 (p : Pattern) (ha : d77316 p = 1) (hb : d82076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d518 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d527 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6810 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5400 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d77305 q = 1) (hb : d82067 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77305, d82067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77305, d82067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5401 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d77306 q = 1) (hb : d82068 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77306, d82068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77306, d82068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77307 q = 1) (hb : d82069 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77307, d82069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77307, d82069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77308 q = 1) (hb : d82070 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77308, d82070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77308, d82070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d614 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d619 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6818 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d5407 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d77312 q = 1) (hb : d82072 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77312, d82072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77312, d82072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5408 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77313 q = 1) (hb : d82073 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77313, d82073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77313, d82073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77314 q = 1) (hb : d82074 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77314, d82074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77314, d82074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77315 q = 1) (hb : d82075 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77315, d82075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77315, d82075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77316 q = 1) (hb : d82076 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77316, d82076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d77316, d82076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro9088 (p : Pattern) (ha : d77660 p = 1) (hb : d82083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6818 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5407 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77312 q = 1) (hb : d82072 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77312, d82072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77312, d82072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5408 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77313 q = 1) (hb : d82073 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77313, d82073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77313, d82073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77314 q = 1) (hb : d82081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77314, d82081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77314, d82081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77315 q = 1) (hb : d82082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77315, d82082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77315, d82082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77660 q = 1) (hb : d82083 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77660, d82083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77660, d82083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9089 (p : Pattern) (ha : d77670 p = 1) (hb : d82093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6856 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5429 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77666 q = 1) (hb : d82089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77666, d82089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77666, d82089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5430 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77667 q = 1) (hb : d82090 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77667, d82090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77667, d82090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77668 q = 1) (hb : d82091 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77668, d82091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77668, d82091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77669 q = 1) (hb : d82092 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77669, d82092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77669, d82092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77670 q = 1) (hb : d82093 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77670, d82093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77670, d82093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9090 (p : Pattern) (ha : d77676 p = 1) (hb : d82099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d510 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77317 q = 1) (hb : d82077 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77317, d82077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9086 q ha hb
    | true =>
      simp only [d77317, d82077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9087 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6831 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77318 q = 1) (hb : d82078 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77318, d82078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77318, d82078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77658 q = 1) (hb : d82079 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77658, d82079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77658, d82079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77659 q = 1) (hb : d82080 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77659, d82080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77659, d82080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77661 q = 1) (hb : d82084 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77661, d82084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77661, d82084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9088 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d77662 q = 1) (hb : d82085 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77662, d82085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77662, d82085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77663 q = 1) (hb : d82086 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77663, d82086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77663, d82086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d77664 q = 1) (hb : d82087 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77664, d82087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77664, d82087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d77665 q = 1) (hb : d82088 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77665, d82088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77665, d82088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77671 q = 1) (hb : d82094 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77671, d82094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77671, d82094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9089 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77672 q = 1) (hb : d82095 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77672, d82095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77672, d82095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77673 q = 1) (hb : d82096 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77673, d82096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77673, d82096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d77674 q = 1) (hb : d82097 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77674, d82097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77674, d82097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d77675 q = 1) (hb : d82098 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77675, d82098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77675, d82098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d77676 q = 1) (hb : d82099 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77676, d82099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77676, d82099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro9091 (p : Pattern) (ha : d77682 p = 1) (hb : d82105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77677 q = 1) (hb : d82100 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77677, d82100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77677, d82100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9090 q ha hb
  have h2 (q : Pattern) (ha : d77678 q = 1) (hb : d82101 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77678, d82101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77678, d82101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77679 q = 1) (hb : d82102 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77679, d82102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77679, d82102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77680 q = 1) (hb : d82103 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77680, d82103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77680, d82103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77681 q = 1) (hb : d82104 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77681, d82104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77681, d82104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77682 q = 1) (hb : d82105 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77682, d82105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77682, d82105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9092 (p : Pattern) (ha : d77364 p = 1) (hb : d82111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d810 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d819 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6888 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6160 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77360 q = 1) (hb : d82107 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77360, d82107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77360, d82107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6161 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d77361 q = 1) (hb : d82108 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77361, d82108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77361, d82108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77362 q = 1) (hb : d82109 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77362, d82109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77362, d82109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77363 q = 1) (hb : d82110 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77363, d82110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77363, d82110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77364 q = 1) (hb : d82111 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77364, d82111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77364, d82111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro9093 (p : Pattern) (ha : d77371 p = 1) (hb : d82116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d819 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6888 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6160 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d77360 q = 1) (hb : d82107 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77360, d82107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77360, d82107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6161 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d77361 q = 1) (hb : d82108 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77361, d82108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77361, d82108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77362 q = 1) (hb : d82109 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77362, d82109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77362, d82109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77363 q = 1) (hb : d82110 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77363, d82110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77363, d82110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d920 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d925 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6896 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d6181 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d77367 q = 1) (hb : d82112 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77367, d82112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77367, d82112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6182 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77368 q = 1) (hb : d82113 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77368, d82113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77368, d82113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77369 q = 1) (hb : d82114 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77369, d82114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77369, d82114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77370 q = 1) (hb : d82115 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77370, d82115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77370, d82115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77371 q = 1) (hb : d82116 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77371, d82116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d77371, d82116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro9094 (p : Pattern) (ha : d77686 p = 1) (hb : d82123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6896 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6181 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77367 q = 1) (hb : d82112 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77367, d82112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77367, d82112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6182 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77368 q = 1) (hb : d82113 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77368, d82113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77368, d82113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77369 q = 1) (hb : d82121 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77369, d82121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77369, d82121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77370 q = 1) (hb : d82122 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77370, d82122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77370, d82122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77686 q = 1) (hb : d82123 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77686, d82123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77686, d82123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9095 (p : Pattern) (ha : d77696 p = 1) (hb : d82133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6934 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6234 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77692 q = 1) (hb : d82129 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77692, d82129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77692, d82129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6235 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77693 q = 1) (hb : d82130 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77693, d82130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77693, d82130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77694 q = 1) (hb : d82131 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77694, d82131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77694, d82131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77695 q = 1) (hb : d82132 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77695, d82132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77695, d82132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77696 q = 1) (hb : d82133 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77696, d82133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77696, d82133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9096 (p : Pattern) (ha : d77702 p = 1) (hb : d82139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d802 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77372 q = 1) (hb : d82117 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77372, d82117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9092 q ha hb
    | true =>
      simp only [d77372, d82117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9093 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6909 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77373 q = 1) (hb : d82118 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77373, d82118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77373, d82118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77684 q = 1) (hb : d82119 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77684, d82119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77684, d82119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77685 q = 1) (hb : d82120 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77685, d82120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77685, d82120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77687 q = 1) (hb : d82124 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77687, d82124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77687, d82124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9094 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d77688 q = 1) (hb : d82125 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77688, d82125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77688, d82125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77689 q = 1) (hb : d82126 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77689, d82126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77689, d82126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d77690 q = 1) (hb : d82127 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77690, d82127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77690, d82127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d77691 q = 1) (hb : d82128 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77691, d82128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77691, d82128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77697 q = 1) (hb : d82134 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77697, d82134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77697, d82134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9095 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77698 q = 1) (hb : d82135 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77698, d82135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77698, d82135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77699 q = 1) (hb : d82136 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77699, d82136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77699, d82136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d77700 q = 1) (hb : d82137 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77700, d82137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77700, d82137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d77701 q = 1) (hb : d82138 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77701, d82138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77701, d82138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d77702 q = 1) (hb : d82139 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77702, d82139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77702, d82139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro9097 (p : Pattern) (ha : d77708 p = 1) (hb : d82145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77703 q = 1) (hb : d82140 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77703, d82140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77703, d82140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9096 q ha hb
  have h2 (q : Pattern) (ha : d77704 q = 1) (hb : d82141 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77704, d82141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77704, d82141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77705 q = 1) (hb : d82142 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77705, d82142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77705, d82142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77706 q = 1) (hb : d82143 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77706, d82143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77706, d82143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77707 q = 1) (hb : d82144 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77707, d82144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77707, d82144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77708 q = 1) (hb : d82145 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77708, d82145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77708, d82145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9098 (p : Pattern) (ha : d77420 p = 1) (hb : d82152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1189 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1198 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6967 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6299 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77416 q = 1) (hb : d82148 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77416, d82148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77416, d82148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6300 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d77417 q = 1) (hb : d82149 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77417, d82149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77417, d82149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77418 q = 1) (hb : d82150 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77418, d82150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77418, d82150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77419 q = 1) (hb : d82151 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77419, d82151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77419, d82151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77420 q = 1) (hb : d82152 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77420, d82152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77420, d82152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro9099 (p : Pattern) (ha : d77427 p = 1) (hb : d82157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1189 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6967 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6299 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d77416 q = 1) (hb : d82148 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77416, d82148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77416, d82148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6300 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d77417 q = 1) (hb : d82149 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77417, d82149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77417, d82149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77418 q = 1) (hb : d82150 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77418, d82150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77418, d82150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77419 q = 1) (hb : d82151 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77419, d82151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77419, d82151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1331 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1336 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d6975 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d6320 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d77423 q = 1) (hb : d82153 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77423, d82153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77423, d82153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6321 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77424 q = 1) (hb : d82154 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77424, d82154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77424, d82154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77425 q = 1) (hb : d82155 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77425, d82155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77425, d82155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77426 q = 1) (hb : d82156 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77426, d82156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77426, d82156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77427 q = 1) (hb : d82157 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77427, d82157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d77427, d82157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro9100 (p : Pattern) (ha : d77713 p = 1) (hb : d82164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6975 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6320 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77423 q = 1) (hb : d82153 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77423, d82153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77423, d82153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6321 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77424 q = 1) (hb : d82154 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77424, d82154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77424, d82154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77425 q = 1) (hb : d82162 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77425, d82162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77425, d82162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77426 q = 1) (hb : d82163 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77426, d82163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77426, d82163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77713 q = 1) (hb : d82164 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77713, d82164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77713, d82164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9101 (p : Pattern) (ha : d77723 p = 1) (hb : d82174 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7013 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6379 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77719 q = 1) (hb : d82170 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77719, d82170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77719, d82170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6380 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77720 q = 1) (hb : d82171 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77720, d82171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77720, d82171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77721 q = 1) (hb : d82172 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77721, d82172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77721, d82172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77722 q = 1) (hb : d82173 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77722, d82173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77722, d82173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77723 q = 1) (hb : d82174 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77723, d82174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77723, d82174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9102 (p : Pattern) (ha : d77729 p = 1) (hb : d82180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1181 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77428 q = 1) (hb : d82158 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77428, d82158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9098 q ha hb
    | true =>
      simp only [d77428, d82158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9099 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6988 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77429 q = 1) (hb : d82159 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77429, d82159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77429, d82159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77711 q = 1) (hb : d82160 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77711, d82160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77711, d82160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77712 q = 1) (hb : d82161 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77712, d82161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77712, d82161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77714 q = 1) (hb : d82165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77714, d82165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77714, d82165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9100 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1371 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d77715 q = 1) (hb : d82166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77715, d82166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77715, d82166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77716 q = 1) (hb : d82167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77716, d82167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77716, d82167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d77717 q = 1) (hb : d82168 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77717, d82168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77717, d82168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d77718 q = 1) (hb : d82169 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77718, d82169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77718, d82169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77724 q = 1) (hb : d82175 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77724, d82175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77724, d82175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9101 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1504 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77725 q = 1) (hb : d82176 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77725, d82176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77725, d82176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77726 q = 1) (hb : d82177 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77726, d82177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77726, d82177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d77727 q = 1) (hb : d82178 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77727, d82178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77727, d82178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d77728 q = 1) (hb : d82179 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77728, d82179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77728, d82179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d77729 q = 1) (hb : d82180 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77729, d82180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77729, d82180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro9103 (p : Pattern) (ha : d77735 p = 1) (hb : d82186 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77730 q = 1) (hb : d82181 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77730, d82181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77730, d82181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9102 q ha hb
  have h2 (q : Pattern) (ha : d77731 q = 1) (hb : d82182 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77731, d82182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77731, d82182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77732 q = 1) (hb : d82183 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77732, d82183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77732, d82183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77733 q = 1) (hb : d82184 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77733, d82184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77733, d82184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77734 q = 1) (hb : d82185 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77734, d82185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77734, d82185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77735 q = 1) (hb : d82186 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77735, d82186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77735, d82186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9104 (p : Pattern) (ha : d77477 p = 1) (hb : d82194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1650 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1659 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7047 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6445 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77473 q = 1) (hb : d82190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77473, d82190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77473, d82190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6446 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d77474 q = 1) (hb : d82191 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77474, d82191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77474, d82191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77475 q = 1) (hb : d82192 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77475, d82192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77475, d82192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77476 q = 1) (hb : d82193 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77476, d82193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77476, d82193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77477 q = 1) (hb : d82194 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77477, d82194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77477, d82194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro9105 (p : Pattern) (ha : d77484 p = 1) (hb : d82199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1650 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1659 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7047 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6445 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d77473 q = 1) (hb : d82190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77473, d82190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77473, d82190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6446 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d77474 q = 1) (hb : d82191 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77474, d82191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77474, d82191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77475 q = 1) (hb : d82192 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77475, d82192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77475, d82192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77476 q = 1) (hb : d82193 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77476, d82193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77476, d82193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1808 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1813 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7055 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d6466 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d77480 q = 1) (hb : d82195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77480, d82195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77480, d82195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6467 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77481 q = 1) (hb : d82196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77481, d82196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77481, d82196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77482 q = 1) (hb : d82197 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77482, d82197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77482, d82197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77483 q = 1) (hb : d82198 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77483, d82198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77483, d82198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77484 q = 1) (hb : d82199 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77484, d82199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d77484, d82199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro9106 (p : Pattern) (ha : d77741 p = 1) (hb : d82206 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7055 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6466 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77480 q = 1) (hb : d82195 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77480, d82195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77480, d82195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6467 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77481 q = 1) (hb : d82196 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77481, d82196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77481, d82196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77482 q = 1) (hb : d82204 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77482, d82204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77482, d82204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77483 q = 1) (hb : d82205 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77483, d82205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77483, d82205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77741 q = 1) (hb : d82206 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77741, d82206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77741, d82206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9107 (p : Pattern) (ha : d77751 p = 1) (hb : d82216 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7093 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6525 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77747 q = 1) (hb : d82212 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77747, d82212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77747, d82212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6526 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77748 q = 1) (hb : d82213 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77748, d82213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77748, d82213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77749 q = 1) (hb : d82214 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77749, d82214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77749, d82214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77750 q = 1) (hb : d82215 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77750, d82215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77750, d82215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77751 q = 1) (hb : d82216 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77751, d82216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77751, d82216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9108 (p : Pattern) (ha : d77757 p = 1) (hb : d82222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77485 q = 1) (hb : d82200 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77485, d82200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9104 q ha hb
    | true =>
      simp only [d77485, d82200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9105 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7068 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77486 q = 1) (hb : d82201 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77486, d82201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77486, d82201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77739 q = 1) (hb : d82202 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77739, d82202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77739, d82202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77740 q = 1) (hb : d82203 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77740, d82203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77740, d82203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77742 q = 1) (hb : d82207 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77742, d82207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77742, d82207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9106 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1848 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d77743 q = 1) (hb : d82208 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77743, d82208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77743, d82208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77744 q = 1) (hb : d82209 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77744, d82209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77744, d82209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d77745 q = 1) (hb : d82210 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77745, d82210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77745, d82210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d77746 q = 1) (hb : d82211 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77746, d82211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77746, d82211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77752 q = 1) (hb : d82217 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77752, d82217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77752, d82217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9107 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77753 q = 1) (hb : d82218 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77753, d82218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77753, d82218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77754 q = 1) (hb : d82219 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77754, d82219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77754, d82219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d77755 q = 1) (hb : d82220 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77755, d82220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77755, d82220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d77756 q = 1) (hb : d82221 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77756, d82221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77756, d82221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d77757 q = 1) (hb : d82222 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77757, d82222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77757, d82222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro9109 (p : Pattern) (ha : d77763 p = 1) (hb : d82228 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77758 q = 1) (hb : d82223 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77758, d82223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77758, d82223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9108 q ha hb
  have h2 (q : Pattern) (ha : d77759 q = 1) (hb : d82224 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77759, d82224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77759, d82224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77760 q = 1) (hb : d82225 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77760, d82225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77760, d82225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77761 q = 1) (hb : d82226 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77761, d82226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77761, d82226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77762 q = 1) (hb : d82227 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77762, d82227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77762, d82227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77763 q = 1) (hb : d82228 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77763, d82228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77763, d82228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9110 (p : Pattern) (ha : d77535 p = 1) (hb : d82237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2133 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2142 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7128 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6592 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77531 q = 1) (hb : d82233 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77531, d82233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77531, d82233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d6593 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d77532 q = 1) (hb : d82234 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77532, d82234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77532, d82234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77533 q = 1) (hb : d82235 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77533, d82235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77533, d82235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77534 q = 1) (hb : d82236 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77534, d82236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77534, d82236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77535 q = 1) (hb : d82237 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77535, d82237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77535, d82237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro9111 (p : Pattern) (ha : d77542 p = 1) (hb : d82242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2133 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2142 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7128 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d6592 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d77531 q = 1) (hb : d82233 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77531, d82233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77531, d82233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d6593 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d77532 q = 1) (hb : d82234 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77532, d82234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77532, d82234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77533 q = 1) (hb : d82235 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77533, d82235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77533, d82235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77534 q = 1) (hb : d82236 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77534, d82236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77534, d82236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d2286 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d2291 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7136 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d6613 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d77538 q = 1) (hb : d82238 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77538, d82238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d77538, d82238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d6614 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77539 q = 1) (hb : d82239 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77539, d82239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77539, d82239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77540 q = 1) (hb : d82240 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77540, d82240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77540, d82240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77541 q = 1) (hb : d82241 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77541, d82241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77541, d82241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77542 q = 1) (hb : d82242 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77542, d82242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d77542, d82242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro9112 (p : Pattern) (ha : d77770 p = 1) (hb : d82249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7136 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6613 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77538 q = 1) (hb : d82238 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77538, d82238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77538, d82238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6614 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77539 q = 1) (hb : d82239 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77539, d82239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77539, d82239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77540 q = 1) (hb : d82247 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77540, d82247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77540, d82247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77541 q = 1) (hb : d82248 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77541, d82248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77541, d82248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77770 q = 1) (hb : d82249 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77770, d82249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77770, d82249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9113 (p : Pattern) (ha : d77780 p = 1) (hb : d82259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7174 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d6672 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77776 q = 1) (hb : d82255 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d77776, d82255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77776, d82255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6673 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77777 q = 1) (hb : d82256 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d77777, d82256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77777, d82256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77778 q = 1) (hb : d82257 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d77778, d82257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77778, d82257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77779 q = 1) (hb : d82258 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d77779, d82258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77779, d82258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77780 q = 1) (hb : d82259 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d77780, d82259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77780, d82259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9114 (p : Pattern) (ha : d77786 p = 1) (hb : d82265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2125 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77543 q = 1) (hb : d82243 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77543, d82243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9110 q ha hb
    | true =>
      simp only [d77543, d82243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9111 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7149 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d77544 q = 1) (hb : d82244 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77544, d82244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77544, d82244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d77768 q = 1) (hb : d82245 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77768, d82245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77768, d82245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77769 q = 1) (hb : d82246 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77769, d82246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77769, d82246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77771 q = 1) (hb : d82250 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77771, d82250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77771, d82250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9112 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2326 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d77772 q = 1) (hb : d82251 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77772, d82251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d77772, d82251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77773 q = 1) (hb : d82252 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77773, d82252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d77773, d82252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d77774 q = 1) (hb : d82253 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77774, d82253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77774, d82253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d77775 q = 1) (hb : d82254 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77775, d82254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77775, d82254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77781 q = 1) (hb : d82260 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d77781, d82260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77781, d82260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9113 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d2459 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d77782 q = 1) (hb : d82261 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d77782, d82261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d77782, d82261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77783 q = 1) (hb : d82262 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d77783, d82262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77783, d82262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d77784 q = 1) (hb : d82263 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d77784, d82263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d77784, d82263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d77785 q = 1) (hb : d82264 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d77785, d82264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d77785, d82264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d77786 q = 1) (hb : d82265 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d77786, d82265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d77786, d82265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro9115 (p : Pattern) (ha : d77792 p = 1) (hb : d82271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77787 q = 1) (hb : d82266 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d77787, d82266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77787, d82266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9114 q ha hb
  have h2 (q : Pattern) (ha : d77788 q = 1) (hb : d82267 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d77788, d82267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77788, d82267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77789 q = 1) (hb : d82268 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d77789, d82268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77789, d82268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77790 q = 1) (hb : d82269 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d77790, d82269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77790, d82269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77791 q = 1) (hb : d82270 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d77791, d82270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77791, d82270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77792 q = 1) (hb : d82271 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d77792, d82271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77792, d82271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9116 (p : Pattern) (ha : d77798 p = 1) (hb : d82277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d77683 q = 1) (hb : d82106 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77683, d82106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9085 q ha hb
    | true =>
      simp only [d77683, d82106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9091 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d77709 q = 1) (hb : d82146 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77709, d82146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77709, d82146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9097 q ha hb
  have h3 (q : Pattern) (ha : d77710 q = 1) (hb : d82147 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77710, d82147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d77710, d82147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77736 q = 1) (hb : d82187 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77736, d82187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77736, d82187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9103 q ha hb
  have h5 (q : Pattern) (ha : d77737 q = 1) (hb : d82188 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77737, d82188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77737, d82188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77738 q = 1) (hb : d82189 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77738, d82189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77738, d82189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77764 q = 1) (hb : d82229 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77764, d82229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77764, d82229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9109 q ha hb
  have h8 (q : Pattern) (ha : d77765 q = 1) (hb : d82230 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77765, d82230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77765, d82230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77766 q = 1) (hb : d82231 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77766, d82231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77766, d82231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77767 q = 1) (hb : d82232 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d77767, d82232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d77767, d82232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77793 q = 1) (hb : d82272 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d77793, d82272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77793, d82272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9115 q ha hb
  have h12 (q : Pattern) (ha : d77794 q = 1) (hb : d82273 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d77794, d82273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77794, d82273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77795 q = 1) (hb : d82274 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d77795, d82274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77795, d82274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d77796 q = 1) (hb : d82275 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d77796, d82275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77796, d82275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77797 q = 1) (hb : d82276 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d77797, d82276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d77797, d82276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77798 q = 1) (hb : d82277 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d77798, d82277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d77798, d82277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro9117 (p : Pattern) (ha : d77804 p = 1) (hb : d82283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77799 q = 1) (hb : d82278 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d77799, d82278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9116 q ha hb
    | true =>
      simp only [d77799, d82278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77800 q = 1) (hb : d82279 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d77800, d82279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77800, d82279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77801 q = 1) (hb : d82280 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d77801, d82280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77801, d82280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77802 q = 1) (hb : d82281 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d77802, d82281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77802, d82281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77803 q = 1) (hb : d82282 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d77803, d82282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77803, d82282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77804 q = 1) (hb : d82283 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d77804, d82283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77804, d82283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9118 (p : Pattern) (ha : d77810 p = 1) (hb : d82289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77805 q = 1) (hb : d82284 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d77805, d82284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9117 q ha hb
    | true =>
      simp only [d77805, d82284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77806 q = 1) (hb : d82285 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d77806, d82285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77806, d82285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77807 q = 1) (hb : d82286 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d77807, d82286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77807, d82286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77808 q = 1) (hb : d82287 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d77808, d82287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77808, d82287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77809 q = 1) (hb : d82288 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d77809, d82288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77809, d82288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77810 q = 1) (hb : d82289 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d77810, d82289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77810, d82289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9119 (p : Pattern) (ha : d77816 p = 1) (hb : d82295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77811 q = 1) (hb : d82290 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d77811, d82290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9118 q ha hb
    | true =>
      simp only [d77811, d82290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77812 q = 1) (hb : d82291 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d77812, d82291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77812, d82291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77813 q = 1) (hb : d82292 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d77813, d82292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77813, d82292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77814 q = 1) (hb : d82293 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d77814, d82293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77814, d82293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77815 q = 1) (hb : d82294 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d77815, d82294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77815, d82294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77816 q = 1) (hb : d82295 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d77816, d82295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77816, d82295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9120 (p : Pattern) (ha : d77822 p = 1) (hb : d82301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77817 q = 1) (hb : d82296 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d77817, d82296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9119 q ha hb
    | true =>
      simp only [d77817, d82296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77818 q = 1) (hb : d82297 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d77818, d82297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77818, d82297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77819 q = 1) (hb : d82298 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d77819, d82298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77819, d82298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77820 q = 1) (hb : d82299 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d77820, d82299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77820, d82299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77821 q = 1) (hb : d82300 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d77821, d82300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77821, d82300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77822 q = 1) (hb : d82301 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d77822, d82301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77822, d82301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9121 (p : Pattern) (ha : d77828 p = 1) (hb : d82307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77823 q = 1) (hb : d82302 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d77823, d82302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9120 q ha hb
    | true =>
      simp only [d77823, d82302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77824 q = 1) (hb : d82303 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d77824, d82303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77824, d82303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77825 q = 1) (hb : d82304 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d77825, d82304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77825, d82304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77826 q = 1) (hb : d82305 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d77826, d82305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77826, d82305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77827 q = 1) (hb : d82306 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d77827, d82306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77827, d82306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77828 q = 1) (hb : d82307 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d77828, d82307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77828, d82307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9122 (p : Pattern) (ha : d77834 p = 1) (hb : d82313 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77829 q = 1) (hb : d82308 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d77829, d82308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9121 q ha hb
    | true =>
      simp only [d77829, d82308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77830 q = 1) (hb : d82309 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d77830, d82309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77830, d82309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77831 q = 1) (hb : d82310 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d77831, d82310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77831, d82310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77832 q = 1) (hb : d82311 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d77832, d82311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77832, d82311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77833 q = 1) (hb : d82312 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d77833, d82312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77833, d82312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77834 q = 1) (hb : d82313 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d77834, d82313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77834, d82313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9123 (p : Pattern) (ha : d77840 p = 1) (hb : d82319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77835 q = 1) (hb : d82314 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d77835, d82314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9122 q ha hb
    | true =>
      simp only [d77835, d82314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d77836 q = 1) (hb : d82315 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d77836, d82315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d77836, d82315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77837 q = 1) (hb : d82316 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d77837, d82316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d77837, d82316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d77838 q = 1) (hb : d82317 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d77838, d82317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d77838, d82317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d77839 q = 1) (hb : d82318 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d77839, d82318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d77839, d82318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d77840 q = 1) (hb : d82319 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d77840, d82319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77840, d82319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro9124 (p : Pattern) (ha : d0 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9125 (p : Pattern) (ha : d0 p = 1) (hb : d62939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62939 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9126 (p : Pattern) (ha : d0 p = 1) (hb : d82320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82320 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9127 (p : Pattern) (ha : d0 p = 1) (hb : d82321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82321 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9128 (p : Pattern) (ha : d0 p = 1) (hb : d82324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82324 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9129 (p : Pattern) (ha : d0 p = 1) (hb : d73493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73493 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9130 (p : Pattern) (ha : d0 p = 1) (hb : d82333 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82333 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9131 (p : Pattern) (ha : d0 p = 1) (hb : d82334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82334 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9132 (p : Pattern) (ha : d0 p = 1) (hb : d82027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82027 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9133 (p : Pattern) (ha : d0 p = 1) (hb : d82319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82319 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9134 (p : Pattern) (ha : d0 p = 1) (hb : d82335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82335 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9135 (p : Pattern) (ha : d0 p = 1) (hb : d82340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82340 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9136 (p : Pattern) (ha : d0 p = 1) (hb : d82347 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82347 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9137 (p : Pattern) (ha : d0 p = 1) (hb : d82350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82350 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9138 (p : Pattern) (ha : d0 p = 1) (hb : d74039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74039 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9139 (p : Pattern) (ha : d0 p = 1) (hb : d82355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82355 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9140 (p : Pattern) (ha : d0 p = 1) (hb : d65090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d65090 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9141 (p : Pattern) (ha : d0 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9142 (p : Pattern) (ha : d0 p = 1) (hb : d82357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82357 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9143 (p : Pattern) (ha : d0 p = 1) (hb : d82360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82360 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9144 (p : Pattern) (ha : d0 p = 1) (hb : d82362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82362 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9145 (p : Pattern) (ha : d0 p = 1) (hb : d66280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66280 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9146 (p : Pattern) (ha : d0 p = 1) (hb : d82363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82363 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9147 (p : Pattern) (ha : d0 p = 1) (hb : d82364 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82364 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9148 (p : Pattern) (ha : d0 p = 1) (hb : d82367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82367 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9149 (p : Pattern) (ha : d0 p = 1) (hb : d82375 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82375 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9150 (p : Pattern) (ha : d0 p = 1) (hb : d82376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82376 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9151 (p : Pattern) (ha : d0 p = 1) (hb : d82381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82381 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9152 (p : Pattern) (ha : d0 p = 1) (hb : d74073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74073 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9153 (p : Pattern) (ha : d0 p = 1) (hb : d82409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82409 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9154 (p : Pattern) (ha : d0 p = 1) (hb : d82414 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82414 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9155 (p : Pattern) (ha : d0 p = 1) (hb : d82415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82415 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9156 (p : Pattern) (ha : d0 p = 1) (hb : d82422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d82422 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9157 (p : Pattern) (ha : d57573 p = 1) (hb : d74579 p = 1) : d67649 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d300 q = 1) (hb : d57573 q = 1) : d300 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306 q = 1) (hb : d57573 q = 1) : d306 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d4371 q = 1) : d4371 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74576 q = 1) : d67646 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74576, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d57573, d74576, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74577 q = 1) : d67647 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74577, d67647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d74577, d67647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d57573 q = 1) (hb : d74578 q = 1) : d67648 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74578, d67648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74578, d67648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d57573 q = 1) (hb : d74579 q = 1) : d67649 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74579, d67649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74579, d67649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9158 (p : Pattern) (ha : d57573 p = 1) (hb : d74583 p = 1) : d67653 p = 1 := by
  have h0 (q : Pattern) (ha : d300 q = 1) (hb : d57573 q = 1) : d300 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d306 q = 1) (hb : d57573 q = 1) : d306 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d4371 q = 1) : d4371 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74576 q = 1) : d67646 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74576, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d57573, d74576, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74577 q = 1) : d67647 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74577, d67647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74577, d67647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74578 q = 1) : d67648 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74578, d67648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74578, d67648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d380 q = 1) (hb : d57573 q = 1) : d380 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d384 q = 1) (hb : d57573 q = 1) : d384 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d4376 q = 1) : d4376 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d57573 q = 1) (hb : d74580 q = 1) : d67650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74580, d67650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d57573, d74580, d67650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d57573 q = 1) (hb : d74581 q = 1) : d67651 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74581, d67651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d74581, d67651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d57573 q = 1) (hb : d74582 q = 1) : d67652 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74582, d67652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74582, d67652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d57573 q = 1) (hb : d74583 q = 1) : d67653 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74583, d67653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74583, d67653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro9159 (p : Pattern) (ha : d57573 p = 1) (hb : d74590 p = 1) : d67660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d4376 q = 1) : d4376 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74580 q = 1) : d67650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74580, d67650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57573, d74580, d67650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74588 q = 1) : d67658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74588, d67658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74588, d67658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74589 q = 1) : d67659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74589, d67659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74589, d67659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74590 q = 1) : d67660 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74590, d67660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74590, d67660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9160 (p : Pattern) (ha : d57573 p = 1) (hb : d74599 p = 1) : d67669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d4391 q = 1) : d4391 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5379 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74596 q = 1) : d67666 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74596, d67666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57573, d74596, d67666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74597 q = 1) : d67667 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74597, d67667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74597, d67667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74598 q = 1) : d67668 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74598, d67668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74598, d67668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74599 q = 1) : d67669 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74599, d67669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74599, d67669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9161 (p : Pattern) (ha : d57573 p = 1) (hb : d74605 p = 1) : d67675 p = 1 := by
  have h0 (q : Pattern) (ha : d294 q = 1) (hb : d57573 q = 1) : d294 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57573 q = 1) (hb : d74584 q = 1) : d67654 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74584, d67654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9157 q ha hb
    | true =>
      simp only [d74584, d67654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9158 q ha hb
  have h2 (q : Pattern) (ha : d398 q = 1) (hb : d57573 q = 1) : d398 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74585 q = 1) : d67655 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74585, d67655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74585, d67655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74586 q = 1) : d67656 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74586, d67656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74586, d67656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74587 q = 1) : d67657 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74587, d67657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74587, d67657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d57573 q = 1) (hb : d74591 q = 1) : d67661 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74591, d67661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74591, d67661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9159 q ha hb
  have h8 (q : Pattern) (ha : d407 q = 1) (hb : d57573 q = 1) : d407 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d57573 q = 1) (hb : d74592 q = 1) : d67662 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74592, d67662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74592, d67662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d57573 q = 1) (hb : d74593 q = 1) : d67663 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74593, d67663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74593, d67663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d57573 q = 1) (hb : d74594 q = 1) : d67664 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74594, d67664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74594, d67664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d57573 q = 1) (hb : d74595 q = 1) : d67665 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74595, d67665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74595, d67665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d57573 q = 1) (hb : d74600 q = 1) : d67670 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74600, d67670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74600, d67670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9160 q ha hb
  have h14 (q : Pattern) (ha : d463 q = 1) (hb : d57573 q = 1) : d463 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d57573 q = 1) (hb : d74601 q = 1) : d67671 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74601, d67671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74601, d67671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d57573 q = 1) (hb : d74602 q = 1) : d67672 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74602, d67672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74602, d67672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d57573 q = 1) (hb : d74603 q = 1) : d67673 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74603, d67673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74603, d67673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d57573 q = 1) (hb : d74604 q = 1) : d67674 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74604, d67674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74604, d67674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d57573 q = 1) (hb : d74605 q = 1) : d67675 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74605, d67675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74605, d67675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro9162 (p : Pattern) (ha : d57573 p = 1) (hb : d74611 p = 1) : d67681 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d57573 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d57573 q = 1) : d67641 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d67641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d67641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3685 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d57573 q = 1) : d67642 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d67642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d67642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d57573 q = 1) : d67643 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d67643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d67643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d57573 q = 1) : d67644 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d67644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d67644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d57573 q = 1) : d67645 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d67645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51657, d67645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d57573 q = 1) (hb : d74606 q = 1) : d67676 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74606, d67676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74606, d67676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9161 q ha hb
  have h8 (q : Pattern) (ha : d57573 q = 1) (hb : d74607 q = 1) : d67677 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74607, d67677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74607, d67677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d57573 q = 1) (hb : d74608 q = 1) : d67678 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74608, d67678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74608, d67678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d57573 q = 1) (hb : d74609 q = 1) : d67679 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74609, d67679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74609, d67679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d57573 q = 1) (hb : d74610 q = 1) : d67680 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74610, d67680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74610, d67680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d57573 q = 1) (hb : d74611 q = 1) : d67681 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74611, d67681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d74611, d67681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro9163 (p : Pattern) (ha : d57573 p = 1) (hb : d74615 p = 1) : d67685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d518 q = 1) (hb : d57573 q = 1) : d518 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d527 q = 1) (hb : d57573 q = 1) : d527 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d4408 q = 1) : d4408 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5401 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74612 q = 1) : d67682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74612, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d57573, d74612, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74613 q = 1) : d67683 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74613, d67683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d74613, d67683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d57573 q = 1) (hb : d74614 q = 1) : d67684 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74614, d67684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74614, d67684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d57573 q = 1) (hb : d74615 q = 1) : d67685 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74615, d67685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74615, d67685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9164 (p : Pattern) (ha : d57573 p = 1) (hb : d74619 p = 1) : d67689 p = 1 := by
  have h0 (q : Pattern) (ha : d518 q = 1) (hb : d57573 q = 1) : d518 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d527 q = 1) (hb : d57573 q = 1) : d527 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d4408 q = 1) : d4408 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5401 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74612 q = 1) : d67682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74612, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d57573, d74612, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74613 q = 1) : d67683 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74613, d67683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74613, d67683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74614 q = 1) : d67684 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74614, d67684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74614, d67684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d614 q = 1) (hb : d57573 q = 1) : d614 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d619 q = 1) (hb : d57573 q = 1) : d619 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d4413 q = 1) : d4413 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5408 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d57573 q = 1) (hb : d74616 q = 1) : d67686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74616, d67686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d57573, d74616, d67686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d57573 q = 1) (hb : d74617 q = 1) : d67687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74617, d67687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d74617, d67687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d57573 q = 1) (hb : d74618 q = 1) : d67688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74618, d67688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74618, d67688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d57573 q = 1) (hb : d74619 q = 1) : d67689 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74619, d67689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74619, d67689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro9165 (p : Pattern) (ha : d57573 p = 1) (hb : d74626 p = 1) : d67696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d4413 q = 1) : d4413 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5408 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74616 q = 1) : d67686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74616, d67686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57573, d74616, d67686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74624 q = 1) : d67694 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74624, d67694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74624, d67694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74625 q = 1) : d67695 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74625, d67695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74625, d67695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74626 q = 1) : d67696 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74626, d67696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74626, d67696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9166 (p : Pattern) (ha : d57573 p = 1) (hb : d74635 p = 1) : d67705 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d4428 q = 1) : d4428 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5430 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74632 q = 1) : d67702 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74632, d67702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57573, d74632, d67702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74633 q = 1) : d67703 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74633, d67703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74633, d67703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74634 q = 1) : d67704 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74634, d67704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74634, d67704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74635 q = 1) : d67705 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74635, d67705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74635, d67705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9167 (p : Pattern) (ha : d57573 p = 1) (hb : d74641 p = 1) : d67711 p = 1 := by
  have h0 (q : Pattern) (ha : d510 q = 1) (hb : d57573 q = 1) : d510 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57573 q = 1) (hb : d74620 q = 1) : d67690 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74620, d67690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9163 q ha hb
    | true =>
      simp only [d74620, d67690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9164 q ha hb
  have h2 (q : Pattern) (ha : d645 q = 1) (hb : d57573 q = 1) : d645 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74621 q = 1) : d67691 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74621, d67691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74621, d67691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74622 q = 1) : d67692 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74622, d67692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74622, d67692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74623 q = 1) : d67693 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74623, d67693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74623, d67693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d57573 q = 1) (hb : d74627 q = 1) : d67697 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74627, d67697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74627, d67697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9165 q ha hb
  have h8 (q : Pattern) (ha : d654 q = 1) (hb : d57573 q = 1) : d654 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d57573 q = 1) (hb : d74628 q = 1) : d67698 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74628, d67698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74628, d67698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d57573 q = 1) (hb : d74629 q = 1) : d67699 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74629, d67699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74629, d67699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d57573 q = 1) (hb : d74630 q = 1) : d67700 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74630, d67700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74630, d67700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d57573 q = 1) (hb : d74631 q = 1) : d67701 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74631, d67701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74631, d67701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d57573 q = 1) (hb : d74636 q = 1) : d67706 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74636, d67706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74636, d67706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9166 q ha hb
  have h14 (q : Pattern) (ha : d737 q = 1) (hb : d57573 q = 1) : d737 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d57573 q = 1) (hb : d74637 q = 1) : d67707 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74637, d67707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74637, d67707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d57573 q = 1) (hb : d74638 q = 1) : d67708 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74638, d67708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74638, d67708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d57573 q = 1) (hb : d74639 q = 1) : d67709 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74639, d67709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74639, d67709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d57573 q = 1) (hb : d74640 q = 1) : d67710 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74640, d67710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74640, d67710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d57573 q = 1) (hb : d74641 q = 1) : d67711 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74641, d67711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74641, d67711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro9168 (p : Pattern) (ha : d57573 p = 1) (hb : d74647 p = 1) : d67717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57573 q = 1) (hb : d74642 q = 1) : d67712 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74642, d67712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74642, d67712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9167 q ha hb
  have h2 (q : Pattern) (ha : d57573 q = 1) (hb : d74643 q = 1) : d67713 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74643, d67713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74643, d67713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74644 q = 1) : d67714 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74644, d67714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74644, d67714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74645 q = 1) : d67715 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74645, d67715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74645, d67715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74646 q = 1) : d67716 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74646, d67716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74646, d67716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74647 q = 1) : d67717 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74647, d67717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74647, d67717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9169 (p : Pattern) (ha : d57573 p = 1) (hb : d74652 p = 1) : d67722 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d810 q = 1) (hb : d57573 q = 1) : d810 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d819 q = 1) (hb : d57573 q = 1) : d819 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d4446 q = 1) : d4446 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5471 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74649 q = 1) : d67719 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74649, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d57573, d74649, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74650 q = 1) : d67720 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74650, d67720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d74650, d67720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d57573 q = 1) (hb : d74651 q = 1) : d67721 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74651, d67721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74651, d67721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d57573 q = 1) (hb : d74652 q = 1) : d67722 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74652, d67722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74652, d67722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9170 (p : Pattern) (ha : d57573 p = 1) (hb : d74656 p = 1) : d67726 p = 1 := by
  have h0 (q : Pattern) (ha : d810 q = 1) (hb : d57573 q = 1) : d810 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d819 q = 1) (hb : d57573 q = 1) : d819 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d4446 q = 1) : d4446 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5471 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74649 q = 1) : d67719 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74649, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d57573, d74649, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74650 q = 1) : d67720 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74650, d67720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74650, d67720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74651 q = 1) : d67721 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74651, d67721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74651, d67721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d920 q = 1) (hb : d57573 q = 1) : d920 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d925 q = 1) (hb : d57573 q = 1) : d925 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d4451 q = 1) : d4451 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5478 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d57573 q = 1) (hb : d74653 q = 1) : d67723 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74653, d67723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d57573, d74653, d67723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d57573 q = 1) (hb : d74654 q = 1) : d67724 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74654, d67724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d74654, d67724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d57573 q = 1) (hb : d74655 q = 1) : d67725 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74655, d67725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74655, d67725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d57573 q = 1) (hb : d74656 q = 1) : d67726 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74656, d67726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74656, d67726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro9171 (p : Pattern) (ha : d57573 p = 1) (hb : d74663 p = 1) : d67733 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d4451 q = 1) : d4451 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5478 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74653 q = 1) : d67723 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74653, d67723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57573, d74653, d67723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74661 q = 1) : d67731 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74661, d67731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74661, d67731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74662 q = 1) : d67732 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74662, d67732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74662, d67732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74663 q = 1) : d67733 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74663, d67733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74663, d67733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9172 (p : Pattern) (ha : d57573 p = 1) (hb : d74672 p = 1) : d67742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d4466 q = 1) : d4466 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5515 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74669 q = 1) : d67739 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74669, d67739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57573, d74669, d67739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74670 q = 1) : d67740 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74670, d67740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74670, d67740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74671 q = 1) : d67741 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74671, d67741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74671, d67741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74672 q = 1) : d67742 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74672, d67742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74672, d67742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9173 (p : Pattern) (ha : d57573 p = 1) (hb : d74678 p = 1) : d67748 p = 1 := by
  have h0 (q : Pattern) (ha : d802 q = 1) (hb : d57573 q = 1) : d802 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57573 q = 1) (hb : d74657 q = 1) : d67727 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74657, d67727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9169 q ha hb
    | true =>
      simp only [d74657, d67727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9170 q ha hb
  have h2 (q : Pattern) (ha : d951 q = 1) (hb : d57573 q = 1) : d951 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74658 q = 1) : d67728 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74658, d67728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74658, d67728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74659 q = 1) : d67729 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74659, d67729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74659, d67729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74660 q = 1) : d67730 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74660, d67730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74660, d67730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d57573 q = 1) (hb : d74664 q = 1) : d67734 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74664, d67734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74664, d67734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9171 q ha hb
  have h8 (q : Pattern) (ha : d960 q = 1) (hb : d57573 q = 1) : d960 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d57573 q = 1) (hb : d74665 q = 1) : d67735 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74665, d67735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74665, d67735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d57573 q = 1) (hb : d74666 q = 1) : d67736 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74666, d67736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74666, d67736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d57573 q = 1) (hb : d74667 q = 1) : d67737 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74667, d67737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74667, d67737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d57573 q = 1) (hb : d74668 q = 1) : d67738 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74668, d67738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74668, d67738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d57573 q = 1) (hb : d74673 q = 1) : d67743 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74673, d67743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74673, d67743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9172 q ha hb
  have h14 (q : Pattern) (ha : d1070 q = 1) (hb : d57573 q = 1) : d1070 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d57573 q = 1) (hb : d74674 q = 1) : d67744 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74674, d67744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74674, d67744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d57573 q = 1) (hb : d74675 q = 1) : d67745 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74675, d67745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74675, d67745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d57573 q = 1) (hb : d74676 q = 1) : d67746 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74676, d67746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74676, d67746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d57573 q = 1) (hb : d74677 q = 1) : d67747 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74677, d67747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74677, d67747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d57573 q = 1) (hb : d74678 q = 1) : d67748 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74678, d67748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74678, d67748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro9174 (p : Pattern) (ha : d57573 p = 1) (hb : d74684 p = 1) : d67754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57573 q = 1) (hb : d74679 q = 1) : d67749 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74679, d67749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74679, d67749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9173 q ha hb
  have h2 (q : Pattern) (ha : d57573 q = 1) (hb : d74680 q = 1) : d67750 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74680, d67750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74680, d67750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74681 q = 1) : d67751 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74681, d67751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74681, d67751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74682 q = 1) : d67752 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74682, d67752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74682, d67752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74683 q = 1) : d67753 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74683, d67753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74683, d67753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74684 q = 1) : d67754 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74684, d67754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74684, d67754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9175 (p : Pattern) (ha : d57573 p = 1) (hb : d74690 p = 1) : d67760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1189 q = 1) (hb : d57573 q = 1) : d1189 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1198 q = 1) (hb : d57573 q = 1) : d1198 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d4485 q = 1) : d4485 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5560 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74687 q = 1) : d67757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74687, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d57573, d74687, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74688 q = 1) : d67758 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74688, d67758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d74688, d67758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d57573 q = 1) (hb : d74689 q = 1) : d67759 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74689, d67759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74689, d67759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d57573 q = 1) (hb : d74690 q = 1) : d67760 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74690, d67760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74690, d67760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9176 (p : Pattern) (ha : d57573 p = 1) (hb : d74694 p = 1) : d67764 p = 1 := by
  have h0 (q : Pattern) (ha : d1189 q = 1) (hb : d57573 q = 1) : d1189 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1198 q = 1) (hb : d57573 q = 1) : d1198 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d4485 q = 1) : d4485 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5560 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74687 q = 1) : d67757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74687, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d57573, d74687, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74688 q = 1) : d67758 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74688, d67758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74688, d67758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74689 q = 1) : d67759 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74689, d67759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74689, d67759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1331 q = 1) (hb : d57573 q = 1) : d1331 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1336 q = 1) (hb : d57573 q = 1) : d1336 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d4490 q = 1) : d4490 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5567 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d57573 q = 1) (hb : d74691 q = 1) : d67761 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74691, d67761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d57573, d74691, d67761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d57573 q = 1) (hb : d74692 q = 1) : d67762 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74692, d67762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d74692, d67762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d57573 q = 1) (hb : d74693 q = 1) : d67763 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74693, d67763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74693, d67763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d57573 q = 1) (hb : d74694 q = 1) : d67764 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74694, d67764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74694, d67764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro9177 (p : Pattern) (ha : d57573 p = 1) (hb : d74701 p = 1) : d67771 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d4490 q = 1) : d4490 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5567 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74691 q = 1) : d67761 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74691, d67761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57573, d74691, d67761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74699 q = 1) : d67769 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74699, d67769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74699, d67769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74700 q = 1) : d67770 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74700, d67770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74700, d67770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74701 q = 1) : d67771 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74701, d67771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74701, d67771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9178 (p : Pattern) (ha : d57573 p = 1) (hb : d74710 p = 1) : d67780 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d4505 q = 1) : d4505 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5604 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74707 q = 1) : d67777 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74707, d67777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57573, d74707, d67777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74708 q = 1) : d67778 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74708, d67778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74708, d67778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74709 q = 1) : d67779 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74709, d67779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74709, d67779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74710 q = 1) : d67780 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74710, d67780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74710, d67780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9179 (p : Pattern) (ha : d57573 p = 1) (hb : d74716 p = 1) : d67786 p = 1 := by
  have h0 (q : Pattern) (ha : d1181 q = 1) (hb : d57573 q = 1) : d1181 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57573 q = 1) (hb : d74695 q = 1) : d67765 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74695, d67765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9175 q ha hb
    | true =>
      simp only [d74695, d67765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9176 q ha hb
  have h2 (q : Pattern) (ha : d1362 q = 1) (hb : d57573 q = 1) : d1362 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74696 q = 1) : d67766 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74696, d67766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74696, d67766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74697 q = 1) : d67767 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74697, d67767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74697, d67767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74698 q = 1) : d67768 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74698, d67768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74698, d67768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d57573 q = 1) (hb : d74702 q = 1) : d67772 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74702, d67772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74702, d67772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9177 q ha hb
  have h8 (q : Pattern) (ha : d1371 q = 1) (hb : d57573 q = 1) : d1371 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d57573 q = 1) (hb : d74703 q = 1) : d67773 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74703, d67773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74703, d67773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d57573 q = 1) (hb : d74704 q = 1) : d67774 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74704, d67774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74704, d67774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d57573 q = 1) (hb : d74705 q = 1) : d67775 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74705, d67775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74705, d67775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d57573 q = 1) (hb : d74706 q = 1) : d67776 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74706, d67776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74706, d67776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d57573 q = 1) (hb : d74711 q = 1) : d67781 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74711, d67781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74711, d67781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9178 q ha hb
  have h14 (q : Pattern) (ha : d1504 q = 1) (hb : d57573 q = 1) : d1504 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d57573 q = 1) (hb : d74712 q = 1) : d67782 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74712, d67782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74712, d67782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d57573 q = 1) (hb : d74713 q = 1) : d67783 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74713, d67783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74713, d67783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d57573 q = 1) (hb : d74714 q = 1) : d67784 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74714, d67784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74714, d67784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d57573 q = 1) (hb : d74715 q = 1) : d67785 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74715, d67785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74715, d67785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d57573 q = 1) (hb : d74716 q = 1) : d67786 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74716, d67786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74716, d67786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro9180 (p : Pattern) (ha : d57573 p = 1) (hb : d74722 p = 1) : d67792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57573 q = 1) (hb : d74717 q = 1) : d67787 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74717, d67787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74717, d67787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9179 q ha hb
  have h2 (q : Pattern) (ha : d57573 q = 1) (hb : d74718 q = 1) : d67788 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74718, d67788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74718, d67788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74719 q = 1) : d67789 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74719, d67789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74719, d67789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74720 q = 1) : d67790 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74720, d67790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74720, d67790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74721 q = 1) : d67791 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74721, d67791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74721, d67791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74722 q = 1) : d67792 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74722, d67792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74722, d67792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9181 (p : Pattern) (ha : d57573 p = 1) (hb : d74729 p = 1) : d67799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1650 q = 1) (hb : d57573 q = 1) : d1650 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1659 q = 1) (hb : d57573 q = 1) : d1659 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d4525 q = 1) : d4525 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5650 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74726 q = 1) : d67796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74726, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d57573, d74726, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74727 q = 1) : d67797 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74727, d67797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d74727, d67797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d57573 q = 1) (hb : d74728 q = 1) : d67798 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74728, d67798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74728, d67798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d57573 q = 1) (hb : d74729 q = 1) : d67799 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74729, d67799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74729, d67799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9182 (p : Pattern) (ha : d57573 p = 1) (hb : d74733 p = 1) : d67803 p = 1 := by
  have h0 (q : Pattern) (ha : d1650 q = 1) (hb : d57573 q = 1) : d1650 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1659 q = 1) (hb : d57573 q = 1) : d1659 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d4525 q = 1) : d4525 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5650 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74726 q = 1) : d67796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74726, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d57573, d74726, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74727 q = 1) : d67797 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74727, d67797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74727, d67797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74728 q = 1) : d67798 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74728, d67798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74728, d67798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1808 q = 1) (hb : d57573 q = 1) : d1808 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1813 q = 1) (hb : d57573 q = 1) : d1813 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d4530 q = 1) : d4530 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5657 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d57573 q = 1) (hb : d74730 q = 1) : d67800 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74730, d67800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d57573, d74730, d67800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d57573 q = 1) (hb : d74731 q = 1) : d67801 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74731, d67801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d74731, d67801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d57573 q = 1) (hb : d74732 q = 1) : d67802 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74732, d67802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74732, d67802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d57573 q = 1) (hb : d74733 q = 1) : d67803 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74733, d67803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74733, d67803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro9183 (p : Pattern) (ha : d57573 p = 1) (hb : d74740 p = 1) : d67810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d4530 q = 1) : d4530 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5657 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74730 q = 1) : d67800 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74730, d67800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57573, d74730, d67800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74738 q = 1) : d67808 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74738, d67808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74738, d67808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74739 q = 1) : d67809 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74739, d67809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74739, d67809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74740 q = 1) : d67810 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74740, d67810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74740, d67810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9184 (p : Pattern) (ha : d57573 p = 1) (hb : d74749 p = 1) : d67819 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d4545 q = 1) : d4545 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5694 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74746 q = 1) : d67816 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74746, d67816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57573, d74746, d67816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74747 q = 1) : d67817 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74747, d67817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74747, d67817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74748 q = 1) : d67818 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74748, d67818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74748, d67818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74749 q = 1) : d67819 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74749, d67819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74749, d67819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9185 (p : Pattern) (ha : d57573 p = 1) (hb : d74755 p = 1) : d67825 p = 1 := by
  have h0 (q : Pattern) (ha : d1642 q = 1) (hb : d57573 q = 1) : d1642 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57573 q = 1) (hb : d74734 q = 1) : d67804 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74734, d67804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9181 q ha hb
    | true =>
      simp only [d74734, d67804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9182 q ha hb
  have h2 (q : Pattern) (ha : d1839 q = 1) (hb : d57573 q = 1) : d1839 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74735 q = 1) : d67805 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74735, d67805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74735, d67805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74736 q = 1) : d67806 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74736, d67806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74736, d67806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74737 q = 1) : d67807 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74737, d67807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74737, d67807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d57573 q = 1) (hb : d74741 q = 1) : d67811 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74741, d67811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74741, d67811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9183 q ha hb
  have h8 (q : Pattern) (ha : d1848 q = 1) (hb : d57573 q = 1) : d1848 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d57573 q = 1) (hb : d74742 q = 1) : d67812 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74742, d67812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74742, d67812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d57573 q = 1) (hb : d74743 q = 1) : d67813 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74743, d67813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74743, d67813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d57573 q = 1) (hb : d74744 q = 1) : d67814 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74744, d67814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74744, d67814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d57573 q = 1) (hb : d74745 q = 1) : d67815 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74745, d67815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74745, d67815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d57573 q = 1) (hb : d74750 q = 1) : d67820 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74750, d67820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74750, d67820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9184 q ha hb
  have h14 (q : Pattern) (ha : d1981 q = 1) (hb : d57573 q = 1) : d1981 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d57573 q = 1) (hb : d74751 q = 1) : d67821 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74751, d67821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74751, d67821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d57573 q = 1) (hb : d74752 q = 1) : d67822 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74752, d67822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74752, d67822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d57573 q = 1) (hb : d74753 q = 1) : d67823 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74753, d67823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74753, d67823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d57573 q = 1) (hb : d74754 q = 1) : d67824 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74754, d67824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74754, d67824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d57573 q = 1) (hb : d74755 q = 1) : d67825 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74755, d67825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74755, d67825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro9186 (p : Pattern) (ha : d57573 p = 1) (hb : d74761 p = 1) : d67831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57573 q = 1) (hb : d74756 q = 1) : d67826 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74756, d67826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74756, d67826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9185 q ha hb
  have h2 (q : Pattern) (ha : d57573 q = 1) (hb : d74757 q = 1) : d67827 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74757, d67827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74757, d67827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74758 q = 1) : d67828 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74758, d67828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74758, d67828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74759 q = 1) : d67829 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74759, d67829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74759, d67829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74760 q = 1) : d67830 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74760, d67830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74760, d67830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74761 q = 1) : d67831 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74761, d67831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74761, d67831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9187 (p : Pattern) (ha : d57573 p = 1) (hb : d74769 p = 1) : d67839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2133 q = 1) (hb : d57573 q = 1) : d2133 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2142 q = 1) (hb : d57573 q = 1) : d2142 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d4566 q = 1) : d4566 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5741 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74766 q = 1) : d67836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74766, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d57573, d74766, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74767 q = 1) : d67837 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74767, d67837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d74767, d67837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d57573 q = 1) (hb : d74768 q = 1) : d67838 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74768, d67838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74768, d67838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d57573 q = 1) (hb : d74769 q = 1) : d67839 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74769, d67839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74769, d67839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro9188 (p : Pattern) (ha : d57573 p = 1) (hb : d74773 p = 1) : d67843 p = 1 := by
  have h0 (q : Pattern) (ha : d2133 q = 1) (hb : d57573 q = 1) : d2133 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2142 q = 1) (hb : d57573 q = 1) : d2142 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d4566 q = 1) : d4566 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d5741 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74766 q = 1) : d67836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74766, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d57573, d74766, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74767 q = 1) : d67837 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74767, d67837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74767, d67837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74768 q = 1) : d67838 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74768, d67838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74768, d67838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2286 q = 1) (hb : d57573 q = 1) : d2286 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2291 q = 1) (hb : d57573 q = 1) : d2291 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1 q = 1) (hb : d4571 q = 1) : d4571 q = 1 := by
    exact hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d5748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d57573 q = 1) (hb : d74770 q = 1) : d67840 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74770, d67840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d57573, d74770, d67840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d57573 q = 1) (hb : d74771 q = 1) : d67841 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74771, d67841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d74771, d67841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d57573 q = 1) (hb : d74772 q = 1) : d67842 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74772, d67842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74772, d67842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d57573 q = 1) (hb : d74773 q = 1) : d67843 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74773, d67843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74773, d67843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro9189 (p : Pattern) (ha : d57573 p = 1) (hb : d74780 p = 1) : d67850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d4571 q = 1) : d4571 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5748 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74770 q = 1) : d67840 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74770, d67840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57573, d74770, d67840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74778 q = 1) : d67848 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74778, d67848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74778, d67848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74779 q = 1) : d67849 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74779, d67849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74779, d67849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74780 q = 1) : d67850 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74780, d67850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74780, d67850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9190 (p : Pattern) (ha : d57573 p = 1) (hb : d74789 p = 1) : d67859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d4586 q = 1) : d4586 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d5785 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74786 q = 1) : d67856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57573, d74786, d67856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57573, d74786, d67856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74787 q = 1) : d67857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74787, d67857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74787, d67857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74788 q = 1) : d67858 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74788, d67858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74788, d67858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74789 q = 1) : d67859 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74789, d67859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74789, d67859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9191 (p : Pattern) (ha : d57573 p = 1) (hb : d74795 p = 1) : d67865 p = 1 := by
  have h0 (q : Pattern) (ha : d2125 q = 1) (hb : d57573 q = 1) : d2125 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57573 q = 1) (hb : d74774 q = 1) : d67844 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74774, d67844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9187 q ha hb
    | true =>
      simp only [d74774, d67844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9188 q ha hb
  have h2 (q : Pattern) (ha : d2317 q = 1) (hb : d57573 q = 1) : d2317 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74775 q = 1) : d67845 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74775, d67845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74775, d67845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74776 q = 1) : d67846 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74776, d67846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74776, d67846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74777 q = 1) : d67847 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74777, d67847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74777, d67847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d57573 q = 1) (hb : d74781 q = 1) : d67851 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74781, d67851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74781, d67851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9189 q ha hb
  have h8 (q : Pattern) (ha : d2326 q = 1) (hb : d57573 q = 1) : d2326 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d57573 q = 1) (hb : d74782 q = 1) : d67852 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74782, d67852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74782, d67852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d57573 q = 1) (hb : d74783 q = 1) : d67853 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74783, d67853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74783, d67853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d57573 q = 1) (hb : d74784 q = 1) : d67854 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74784, d67854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74784, d67854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d57573 q = 1) (hb : d74785 q = 1) : d67855 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74785, d67855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74785, d67855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d57573 q = 1) (hb : d74790 q = 1) : d67860 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74790, d67860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74790, d67860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9190 q ha hb
  have h14 (q : Pattern) (ha : d2459 q = 1) (hb : d57573 q = 1) : d2459 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d57573 q = 1) (hb : d74791 q = 1) : d67861 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74791, d67861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74791, d67861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d57573 q = 1) (hb : d74792 q = 1) : d67862 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74792, d67862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74792, d67862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d57573 q = 1) (hb : d74793 q = 1) : d67863 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74793, d67863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74793, d67863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d57573 q = 1) (hb : d74794 q = 1) : d67864 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74794, d67864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74794, d67864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d57573 q = 1) (hb : d74795 q = 1) : d67865 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74795, d67865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74795, d67865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro9192 (p : Pattern) (ha : d57573 p = 1) (hb : d74801 p = 1) : d67871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57573 q = 1) (hb : d74796 q = 1) : d67866 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74796, d67866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74796, d67866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9191 q ha hb
  have h2 (q : Pattern) (ha : d57573 q = 1) (hb : d74797 q = 1) : d67867 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74797, d67867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74797, d67867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74798 q = 1) : d67868 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74798, d67868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74798, d67868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74799 q = 1) : d67869 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74799, d67869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74799, d67869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74800 q = 1) : d67870 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74800, d67870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74800, d67870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74801 q = 1) : d67871 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74801, d67871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74801, d67871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9193 (p : Pattern) (ha : d57573 p = 1) (hb : d74807 p = 1) : d67877 p = 1 := by
  have h0 (q : Pattern) (ha : d57573 q = 1) (hb : d74648 q = 1) : d67718 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74648, d67718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9162 q ha hb
    | true =>
      simp only [d74648, d67718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9168 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d57573 q = 1) (hb : d74685 q = 1) : d67755 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74685, d67755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74685, d67755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9174 q ha hb
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74686 q = 1) : d67756 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74686, d67756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74686, d67756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74723 q = 1) : d67793 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74723, d67793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74723, d67793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9180 q ha hb
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74724 q = 1) : d67794 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74724, d67794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74724, d67794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74725 q = 1) : d67795 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74725, d67795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74725, d67795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d57573 q = 1) (hb : d74762 q = 1) : d67832 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74762, d67832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74762, d67832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9186 q ha hb
  have h8 (q : Pattern) (ha : d57573 q = 1) (hb : d74763 q = 1) : d67833 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74763, d67833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74763, d67833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d57573 q = 1) (hb : d74764 q = 1) : d67834 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74764, d67834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74764, d67834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d57573 q = 1) (hb : d74765 q = 1) : d67835 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74765, d67835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74765, d67835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d57573 q = 1) (hb : d74802 q = 1) : d67872 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74802, d67872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74802, d67872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9192 q ha hb
  have h12 (q : Pattern) (ha : d57573 q = 1) (hb : d74803 q = 1) : d67873 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74803, d67873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74803, d67873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d57573 q = 1) (hb : d74804 q = 1) : d67874 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74804, d67874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74804, d67874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d57573 q = 1) (hb : d74805 q = 1) : d67875 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74805, d67875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74805, d67875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d57573 q = 1) (hb : d74806 q = 1) : d67876 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d74806, d67876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74806, d67876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d57573 q = 1) (hb : d74807 q = 1) : d67877 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d74807, d67877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74807, d67877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro9194 (p : Pattern) (ha : d57573 p = 1) (hb : d74813 p = 1) : d67883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57573 q = 1) (hb : d74808 q = 1) : d67878 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d74808, d67878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9193 q ha hb
    | true =>
      simp only [d74808, d67878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d57573 q = 1) (hb : d74809 q = 1) : d67879 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d74809, d67879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74809, d67879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74810 q = 1) : d67880 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d74810, d67880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74810, d67880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74811 q = 1) : d67881 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d74811, d67881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74811, d67881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74812 q = 1) : d67882 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d74812, d67882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74812, d67882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74813 q = 1) : d67883 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d74813, d67883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74813, d67883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro9195 (p : Pattern) (ha : d57573 p = 1) (hb : d74819 p = 1) : d67889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57573 q = 1) (hb : d74814 q = 1) : d67884 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d74814, d67884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9194 q ha hb
    | true =>
      simp only [d74814, d67884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d57573 q = 1) (hb : d74815 q = 1) : d67885 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d74815, d67885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74815, d67885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74816 q = 1) : d67886 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d74816, d67886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74816, d67886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74817 q = 1) : d67887 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d74817, d67887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74817, d67887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74818 q = 1) : d67888 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d74818, d67888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74818, d67888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74819 q = 1) : d67889 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d74819, d67889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74819, d67889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro9196 (p : Pattern) (ha : d57573 p = 1) (hb : d74825 p = 1) : d67895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57573 q = 1) (hb : d74820 q = 1) : d67890 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d74820, d67890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9195 q ha hb
    | true =>
      simp only [d74820, d67890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d57573 q = 1) (hb : d74821 q = 1) : d67891 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d74821, d67891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74821, d67891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74822 q = 1) : d67892 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d74822, d67892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74822, d67892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74823 q = 1) : d67893 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d74823, d67893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74823, d67893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74824 q = 1) : d67894 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d74824, d67894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74824, d67894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74825 q = 1) : d67895 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d74825, d67895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74825, d67895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro9197 (p : Pattern) (ha : d57573 p = 1) (hb : d74831 p = 1) : d67901 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57573 q = 1) (hb : d74826 q = 1) : d67896 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d74826, d67896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9196 q ha hb
    | true =>
      simp only [d74826, d67896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d57573 q = 1) (hb : d74827 q = 1) : d67897 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d74827, d67897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74827, d67897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74828 q = 1) : d67898 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d74828, d67898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74828, d67898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d57573 q = 1) (hb : d74829 q = 1) : d67899 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d74829, d67899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74829, d67899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d57573 q = 1) (hb : d74830 q = 1) : d67900 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d74830, d67900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74830, d67900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d57573 q = 1) (hb : d74831 q = 1) : d67901 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d74831, d67901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74831, d67901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro9198 (p : Pattern) (ha : d74075 p = 1) (hb : d74837 p = 1) : d67907 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57573 q = 1) (hb : d74832 q = 1) : d67902 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d74832, d67902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9197 q ha hb
    | true =>
      simp only [d74832, d67902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d57573 q = 1) (hb : d74833 q = 1) : d67903 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d74833, d67903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74833, d67903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d57573 q = 1) (hb : d74834 q = 1) : d67904 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d74834, d67904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74834, d67904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74075 q = 1) (hb : d74835 q = 1) : d67905 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d74075, d74835, d67905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74075, d74835, d67905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74075 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d74075 q = 1) (hb : d74836 q = 1) : d67906 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74836, d67906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74836, d67906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d74075 q = 1) (hb : d74837 q = 1) : d67907 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d74837, d67907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74837, d67907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h8 p ha hb
theorem andIntro9199 (p : Pattern) (ha : d74075 p = 1) (hb : d74843 p = 1) : d67913 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74075 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74075 q = 1) (hb : d74838 q = 1) : d67908 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74838, d67908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9198 q ha hb
    | true =>
      simp only [d74838, d67908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74075 q = 1) (hb : d74839 q = 1) : d67909 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74839, d67909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74839, d67909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74075 q = 1) (hb : d74840 q = 1) : d67910 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d74840, d67910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74840, d67910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74075 q = 1) (hb : d74841 q = 1) : d67911 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74841, d67911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74841, d67911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74075 q = 1) (hb : d74842 q = 1) : d67912 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74842, d67912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74842, d67912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74075 q = 1) (hb : d74843 q = 1) : d67913 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d74843, d67913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74843, d67913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro9200 (p : Pattern) (ha : d74075 p = 1) (hb : d74849 p = 1) : d67919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74075 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74075 q = 1) (hb : d74844 q = 1) : d67914 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74844, d67914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9199 q ha hb
    | true =>
      simp only [d74844, d67914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74075 q = 1) (hb : d74845 q = 1) : d67915 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74845, d67915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74845, d67915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74075 q = 1) (hb : d74846 q = 1) : d67916 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74846, d67916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74846, d67916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74075 q = 1) (hb : d74847 q = 1) : d67917 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74847, d67917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74847, d67917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74075 q = 1) (hb : d74848 q = 1) : d67918 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74848, d67918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74848, d67918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74075 q = 1) (hb : d74849 q = 1) : d67919 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d74849, d67919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74849, d67919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro9201 (p : Pattern) (ha : d57572 p = 1) (hb : d74579 p = 1) : d82426 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d298 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d299 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d299, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d300 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d305 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d306 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d306, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4371 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d5350 q = 1) : d5350 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d57572 q = 1) (hb : d74576 q = 1) : d82423 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74576, d82423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d57572, d74576, d82423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d57572 q = 1) (hb : d74577 q = 1) : d82424 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74577, d82424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d74577, d82424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d57572 q = 1) (hb : d74578 q = 1) : d82425 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74578, d82425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74578, d82425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d57572 q = 1) (hb : d74579 q = 1) : d82426 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74579, d82426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74579, d82426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro9202 (p : Pattern) (ha : d57572 p = 1) (hb : d74583 p = 1) : d82430 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d298 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d299 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d299, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d300 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d305 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d306 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d306, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4371 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d5350 q = 1) : d5350 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d57572 q = 1) (hb : d74576 q = 1) : d82423 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74576, d82423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d57572, d74576, d82423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d57572 q = 1) (hb : d74577 q = 1) : d82424 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74577, d82424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d74577, d82424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d57572 q = 1) (hb : d74578 q = 1) : d82425 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74578, d82425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74578, d82425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d378 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d379 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d379, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d380 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d383 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d384 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d384, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d4376 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d5357 q = 1) : d5357 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d57572 q = 1) (hb : d74580 q = 1) : d82427 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74580, d82427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d57572, d74580, d82427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d57572 q = 1) (hb : d74581 q = 1) : d82428 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74581, d82428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d74581, d82428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d57572 q = 1) (hb : d74582 q = 1) : d82429 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74582, d82429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d74582, d82429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d57572 q = 1) (hb : d74583 q = 1) : d82430 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74583, d82430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74583, d82430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro9203 (p : Pattern) (ha : d57572 p = 1) (hb : d74590 p = 1) : d82435 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4376 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d5357 q = 1) : d5357 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74580 q = 1) : d82427 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74580, d82427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57572, d74580, d82427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57572 q = 1) (hb : d74588 q = 1) : d82428 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74588, d82428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74588, d82428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57572 q = 1) (hb : d74589 q = 1) : d82429 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74589, d82429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74589, d82429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74590 q = 1) : d82435 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74590, d82435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74590, d82435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9204 (p : Pattern) (ha : d57572 p = 1) (hb : d74599 p = 1) : d82444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4391 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d5379 q = 1) : d5379 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74596 q = 1) : d82441 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74596, d82441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57572, d74596, d82441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57572 q = 1) (hb : d74597 q = 1) : d82442 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74597, d82442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74597, d82442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57572 q = 1) (hb : d74598 q = 1) : d82443 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74598, d82443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74598, d82443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74599 q = 1) : d82444 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74599, d82444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74599, d82444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9205 (p : Pattern) (ha : d57572 p = 1) (hb : d74605 p = 1) : d82450 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3891 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3891 q ha hb
    | true =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3892 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74584 q = 1) : d82431 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74584, d82431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9201 q ha hb
    | true =>
      simp only [d74584, d82431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9202 q ha hb
  have h7 (q : Pattern) (ha : d398 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3893 q ha hb
    | true =>
      simp only [d398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3884 q ha hb
  have h8 (q : Pattern) (ha : d57572 q = 1) (hb : d74585 q = 1) : d82432 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74585, d82432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74585, d82432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d57572 q = 1) (hb : d74586 q = 1) : d82433 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74586, d82433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74586, d82433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d57572 q = 1) (hb : d74587 q = 1) : d82434 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74587, d82434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d74587, d82434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d57572 q = 1) (hb : d74591 q = 1) : d82436 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74591, d82436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74591, d82436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9203 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3894 q ha hb
  have h13 (q : Pattern) (ha : d57572 q = 1) (hb : d74592 q = 1) : d82437 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74592, d82437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74592, d82437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d57572 q = 1) (hb : d74593 q = 1) : d82438 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74593, d82438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74593, d82438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d57572 q = 1) (hb : d74594 q = 1) : d82439 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74594, d82439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74594, d82439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d57572 q = 1) (hb : d74595 q = 1) : d82440 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74595, d82440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74595, d82440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d57572 q = 1) (hb : d74600 q = 1) : d82445 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74600, d82445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74600, d82445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9204 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3895 q ha hb
  have h19 (q : Pattern) (ha : d57572 q = 1) (hb : d74601 q = 1) : d82446 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74601, d82446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74601, d82446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d57572 q = 1) (hb : d74602 q = 1) : d82447 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74602, d82447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74602, d82447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d57572 q = 1) (hb : d74603 q = 1) : d82448 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74603, d82448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74603, d82448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d57572 q = 1) (hb : d74604 q = 1) : d82449 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74604, d82449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74604, d82449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d57572 q = 1) (hb : d74605 q = 1) : d82450 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74605, d82450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74605, d82450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro9206 (p : Pattern) (ha : d57572 p = 1) (hb : d74611 p = 1) : d82456 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3882 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51653 q = 1) (hb : d57572 q = 1) : d67953 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d67953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51653, d67953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3890 q ha hb
  have h6 (q : Pattern) (ha : d51654 q = 1) (hb : d57572 q = 1) : d67954 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d67954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51654, d67954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51655 q = 1) (hb : d57572 q = 1) : d67955 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d67955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51655, d67955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51656 q = 1) (hb : d57572 q = 1) : d67956 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d67956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51656, d67956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51657 q = 1) (hb : d57572 q = 1) : d67957 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d67957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51657, d67957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d57572 q = 1) (hb : d74606 q = 1) : d82451 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74606, d82451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74606, d82451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9205 q ha hb
  have h11 (q : Pattern) (ha : d57572 q = 1) (hb : d74607 q = 1) : d82452 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74607, d82452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74607, d82452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d57572 q = 1) (hb : d74608 q = 1) : d82453 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74608, d82453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74608, d82453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d57572 q = 1) (hb : d74609 q = 1) : d82454 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74609, d82454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74609, d82454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d57572 q = 1) (hb : d74610 q = 1) : d82455 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74610, d82455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74610, d82455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d57572 q = 1) (hb : d74611 q = 1) : d82456 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74611, d82456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d74611, d82456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro9207 (p : Pattern) (ha : d57572 p = 1) (hb : d74615 p = 1) : d82460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d516 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d517 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d517, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d518 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d526 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d527 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d527, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4408 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d5401 q = 1) : d5401 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d57572 q = 1) (hb : d74612 q = 1) : d82457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74612, d82457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d57572, d74612, d82457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d57572 q = 1) (hb : d74613 q = 1) : d82458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74613, d82458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d74613, d82458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d57572 q = 1) (hb : d74614 q = 1) : d82459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74614, d82459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74614, d82459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d57572 q = 1) (hb : d74615 q = 1) : d82460 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74615, d82460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74615, d82460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro9208 (p : Pattern) (ha : d57572 p = 1) (hb : d74619 p = 1) : d82464 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d516 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d517 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d517, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d518 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d526 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d527 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d527, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4408 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d5401 q = 1) : d5401 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d57572 q = 1) (hb : d74612 q = 1) : d82457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74612, d82457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d57572, d74612, d82457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d57572 q = 1) (hb : d74613 q = 1) : d82458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74613, d82458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d74613, d82458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d57572 q = 1) (hb : d74614 q = 1) : d82459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74614, d82459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74614, d82459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d612 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d613 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d613, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d613, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d614 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d618 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d619 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d619, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d619, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d4413 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d5408 q = 1) : d5408 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d57572 q = 1) (hb : d74616 q = 1) : d82461 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74616, d82461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d57572, d74616, d82461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d57572 q = 1) (hb : d74617 q = 1) : d82462 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74617, d82462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d74617, d82462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d57572 q = 1) (hb : d74618 q = 1) : d82463 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74618, d82463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d74618, d82463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d57572 q = 1) (hb : d74619 q = 1) : d82464 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74619, d82464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74619, d82464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro9209 (p : Pattern) (ha : d57572 p = 1) (hb : d74626 p = 1) : d82469 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4413 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d5408 q = 1) : d5408 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74616 q = 1) : d82461 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74616, d82461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57572, d74616, d82461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57572 q = 1) (hb : d74624 q = 1) : d82462 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74624, d82462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74624, d82462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57572 q = 1) (hb : d74625 q = 1) : d82463 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74625, d82463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74625, d82463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74626 q = 1) : d82469 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74626, d82469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74626, d82469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9210 (p : Pattern) (ha : d57572 p = 1) (hb : d74635 p = 1) : d82478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4428 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d5430 q = 1) : d5430 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74632 q = 1) : d82475 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74632, d82475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57572, d74632, d82475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57572 q = 1) (hb : d74633 q = 1) : d82476 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74633, d82476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74633, d82476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57572 q = 1) (hb : d74634 q = 1) : d82477 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74634, d82477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74634, d82477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74635 q = 1) : d82478 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74635, d82478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74635, d82478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9211 (p : Pattern) (ha : d57572 p = 1) (hb : d74641 p = 1) : d82484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3902 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d508 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3902 q ha hb
    | true =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3903 q ha hb
  have h4 (q : Pattern) (ha : d509 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d510 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74620 q = 1) : d82465 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74620, d82465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9207 q ha hb
    | true =>
      simp only [d74620, d82465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9208 q ha hb
  have h7 (q : Pattern) (ha : d645 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3904 q ha hb
    | true =>
      simp only [d645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3905 q ha hb
  have h8 (q : Pattern) (ha : d57572 q = 1) (hb : d74621 q = 1) : d82466 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74621, d82466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74621, d82466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d57572 q = 1) (hb : d74622 q = 1) : d82467 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74622, d82467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74622, d82467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d57572 q = 1) (hb : d74623 q = 1) : d82468 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74623, d82468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d74623, d82468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d57572 q = 1) (hb : d74627 q = 1) : d82470 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74627, d82470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74627, d82470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9209 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3906 q ha hb
  have h13 (q : Pattern) (ha : d57572 q = 1) (hb : d74628 q = 1) : d82471 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74628, d82471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74628, d82471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d57572 q = 1) (hb : d74629 q = 1) : d82472 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74629, d82472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74629, d82472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d57572 q = 1) (hb : d74630 q = 1) : d82473 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74630, d82473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74630, d82473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d57572 q = 1) (hb : d74631 q = 1) : d82474 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74631, d82474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74631, d82474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d57572 q = 1) (hb : d74636 q = 1) : d82479 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74636, d82479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74636, d82479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9210 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3907 q ha hb
  have h19 (q : Pattern) (ha : d57572 q = 1) (hb : d74637 q = 1) : d82480 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74637, d82480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74637, d82480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d57572 q = 1) (hb : d74638 q = 1) : d82481 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74638, d82481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74638, d82481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d57572 q = 1) (hb : d74639 q = 1) : d82482 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74639, d82482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74639, d82482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d57572 q = 1) (hb : d74640 q = 1) : d82483 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74640, d82483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74640, d82483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d57572 q = 1) (hb : d74641 q = 1) : d82484 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74641, d82484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74641, d82484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro9212 (p : Pattern) (ha : d57572 p = 1) (hb : d74647 p = 1) : d82490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57572 q = 1) (hb : d74642 q = 1) : d82485 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74642, d82485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74642, d82485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9211 q ha hb
  have h2 (q : Pattern) (ha : d57572 q = 1) (hb : d74643 q = 1) : d82486 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74643, d82486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74643, d82486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74644 q = 1) : d82487 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74644, d82487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74644, d82487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57572 q = 1) (hb : d74645 q = 1) : d82488 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74645, d82488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74645, d82488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57572 q = 1) (hb : d74646 q = 1) : d82489 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74646, d82489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74646, d82489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74647 q = 1) : d82490 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74647, d82490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74647, d82490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9213 (p : Pattern) (ha : d57572 p = 1) (hb : d74652 p = 1) : d82495 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d808 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d809 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d809, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d810 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d818 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d819 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d819, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4446 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d5471 q = 1) : d5471 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d57572 q = 1) (hb : d74649 q = 1) : d82492 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74649, d82492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d57572, d74649, d82492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d57572 q = 1) (hb : d74650 q = 1) : d82493 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74650, d82493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d74650, d82493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d57572 q = 1) (hb : d74651 q = 1) : d82494 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74651, d82494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74651, d82494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d57572 q = 1) (hb : d74652 q = 1) : d82495 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74652, d82495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74652, d82495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro9214 (p : Pattern) (ha : d57572 p = 1) (hb : d74656 p = 1) : d82499 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d808 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d809 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d809, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d810 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d818 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d819 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d819, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4446 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d5471 q = 1) : d5471 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d57572 q = 1) (hb : d74649 q = 1) : d82492 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74649, d82492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d57572, d74649, d82492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d57572 q = 1) (hb : d74650 q = 1) : d82493 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74650, d82493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d74650, d82493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d57572 q = 1) (hb : d74651 q = 1) : d82494 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74651, d82494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74651, d82494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d918 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d919 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d919, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d919, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d920 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d924 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d925 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d925, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d925, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d4451 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d5478 q = 1) : d5478 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d57572 q = 1) (hb : d74653 q = 1) : d82496 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74653, d82496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d57572, d74653, d82496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d57572 q = 1) (hb : d74654 q = 1) : d82497 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74654, d82497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d74654, d82497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d57572 q = 1) (hb : d74655 q = 1) : d82498 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74655, d82498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d74655, d82498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d57572 q = 1) (hb : d74656 q = 1) : d82499 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74656, d82499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74656, d82499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro9215 (p : Pattern) (ha : d57572 p = 1) (hb : d74663 p = 1) : d82504 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4451 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d5478 q = 1) : d5478 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74653 q = 1) : d82496 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74653, d82496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57572, d74653, d82496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57572 q = 1) (hb : d74661 q = 1) : d82497 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74661, d82497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74661, d82497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57572 q = 1) (hb : d74662 q = 1) : d82498 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74662, d82498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74662, d82498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74663 q = 1) : d82504 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74663, d82504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74663, d82504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9216 (p : Pattern) (ha : d57572 p = 1) (hb : d74672 p = 1) : d82513 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4466 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d5515 q = 1) : d5515 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74669 q = 1) : d82510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74669, d82510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57572, d74669, d82510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57572 q = 1) (hb : d74670 q = 1) : d82511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74670, d82511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74670, d82511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57572 q = 1) (hb : d74671 q = 1) : d82512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74671, d82512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74671, d82512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74672 q = 1) : d82513 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74672, d82513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74672, d82513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9217 (p : Pattern) (ha : d57572 p = 1) (hb : d74678 p = 1) : d82519 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3914 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3914 q ha hb
    | true =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3915 q ha hb
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d802 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74657 q = 1) : d82500 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74657, d82500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9213 q ha hb
    | true =>
      simp only [d74657, d82500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9214 q ha hb
  have h7 (q : Pattern) (ha : d951 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3916 q ha hb
    | true =>
      simp only [d951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3917 q ha hb
  have h8 (q : Pattern) (ha : d57572 q = 1) (hb : d74658 q = 1) : d82501 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74658, d82501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74658, d82501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d57572 q = 1) (hb : d74659 q = 1) : d82502 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74659, d82502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74659, d82502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d57572 q = 1) (hb : d74660 q = 1) : d82503 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74660, d82503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d74660, d82503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d57572 q = 1) (hb : d74664 q = 1) : d82505 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74664, d82505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74664, d82505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9215 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3918 q ha hb
  have h13 (q : Pattern) (ha : d57572 q = 1) (hb : d74665 q = 1) : d82506 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74665, d82506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74665, d82506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d57572 q = 1) (hb : d74666 q = 1) : d82507 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74666, d82507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74666, d82507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d57572 q = 1) (hb : d74667 q = 1) : d82508 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74667, d82508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74667, d82508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d57572 q = 1) (hb : d74668 q = 1) : d82509 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74668, d82509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74668, d82509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d57572 q = 1) (hb : d74673 q = 1) : d82514 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74673, d82514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74673, d82514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9216 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3919 q ha hb
  have h19 (q : Pattern) (ha : d57572 q = 1) (hb : d74674 q = 1) : d82515 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74674, d82515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74674, d82515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d57572 q = 1) (hb : d74675 q = 1) : d82516 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74675, d82516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74675, d82516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d57572 q = 1) (hb : d74676 q = 1) : d82517 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74676, d82517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74676, d82517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d57572 q = 1) (hb : d74677 q = 1) : d82518 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74677, d82518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74677, d82518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d57572 q = 1) (hb : d74678 q = 1) : d82519 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74678, d82519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74678, d82519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro9218 (p : Pattern) (ha : d57572 p = 1) (hb : d74684 p = 1) : d82525 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57572 q = 1) (hb : d74679 q = 1) : d82520 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74679, d82520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74679, d82520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9217 q ha hb
  have h2 (q : Pattern) (ha : d57572 q = 1) (hb : d74680 q = 1) : d82521 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74680, d82521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74680, d82521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74681 q = 1) : d82522 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74681, d82522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74681, d82522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57572 q = 1) (hb : d74682 q = 1) : d82523 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74682, d82523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74682, d82523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57572 q = 1) (hb : d74683 q = 1) : d82524 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74683, d82524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74683, d82524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74684 q = 1) : d82525 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74684, d82525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74684, d82525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9219 (p : Pattern) (ha : d57572 p = 1) (hb : d74690 p = 1) : d82531 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1187 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1188 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1188, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1189 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1197 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1198 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1198, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4485 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d5560 q = 1) : d5560 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d57572 q = 1) (hb : d74687 q = 1) : d82528 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74687, d82528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d57572, d74687, d82528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d57572 q = 1) (hb : d74688 q = 1) : d82529 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74688, d82529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d74688, d82529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d57572 q = 1) (hb : d74689 q = 1) : d82530 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74689, d82530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74689, d82530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d57572 q = 1) (hb : d74690 q = 1) : d82531 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74690, d82531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74690, d82531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro9220 (p : Pattern) (ha : d57572 p = 1) (hb : d74694 p = 1) : d82535 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1187 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1188 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1188, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1189 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1197 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1198 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1198, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4485 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d5560 q = 1) : d5560 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d57572 q = 1) (hb : d74687 q = 1) : d82528 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74687, d82528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d57572, d74687, d82528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d57572 q = 1) (hb : d74688 q = 1) : d82529 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74688, d82529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d74688, d82529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d57572 q = 1) (hb : d74689 q = 1) : d82530 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74689, d82530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74689, d82530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d1329 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1330 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1330, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d1330, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d1331 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d1335 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d1336 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1336, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d1336, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d4490 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d5567 q = 1) : d5567 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d57572 q = 1) (hb : d74691 q = 1) : d82532 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74691, d82532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d57572, d74691, d82532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d57572 q = 1) (hb : d74692 q = 1) : d82533 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74692, d82533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d74692, d82533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d57572 q = 1) (hb : d74693 q = 1) : d82534 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74693, d82534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d74693, d82534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d57572 q = 1) (hb : d74694 q = 1) : d82535 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74694, d82535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74694, d82535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro9221 (p : Pattern) (ha : d57572 p = 1) (hb : d74701 p = 1) : d82540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4490 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d5567 q = 1) : d5567 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74691 q = 1) : d82532 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74691, d82532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57572, d74691, d82532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57572 q = 1) (hb : d74699 q = 1) : d82533 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74699, d82533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74699, d82533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57572 q = 1) (hb : d74700 q = 1) : d82534 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74700, d82534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74700, d82534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74701 q = 1) : d82540 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74701, d82540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74701, d82540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9222 (p : Pattern) (ha : d57572 p = 1) (hb : d74710 p = 1) : d82549 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4505 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d5604 q = 1) : d5604 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74707 q = 1) : d82546 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74707, d82546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57572, d74707, d82546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57572 q = 1) (hb : d74708 q = 1) : d82547 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74708, d82547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74708, d82547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57572 q = 1) (hb : d74709 q = 1) : d82548 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74709, d82548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74709, d82548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74710 q = 1) : d82549 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74710, d82549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74710, d82549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9223 (p : Pattern) (ha : d57572 p = 1) (hb : d74716 p = 1) : d82555 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3926 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3926 q ha hb
    | true =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3927 q ha hb
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1181 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74695 q = 1) : d82536 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74695, d82536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9219 q ha hb
    | true =>
      simp only [d74695, d82536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9220 q ha hb
  have h7 (q : Pattern) (ha : d1362 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3928 q ha hb
    | true =>
      simp only [d1362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3929 q ha hb
  have h8 (q : Pattern) (ha : d57572 q = 1) (hb : d74696 q = 1) : d82537 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74696, d82537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74696, d82537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d57572 q = 1) (hb : d74697 q = 1) : d82538 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74697, d82538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74697, d82538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d57572 q = 1) (hb : d74698 q = 1) : d82539 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74698, d82539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d74698, d82539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d57572 q = 1) (hb : d74702 q = 1) : d82541 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74702, d82541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74702, d82541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9221 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3930 q ha hb
  have h13 (q : Pattern) (ha : d57572 q = 1) (hb : d74703 q = 1) : d82542 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74703, d82542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74703, d82542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d57572 q = 1) (hb : d74704 q = 1) : d82543 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74704, d82543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74704, d82543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d57572 q = 1) (hb : d74705 q = 1) : d82544 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74705, d82544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74705, d82544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d57572 q = 1) (hb : d74706 q = 1) : d82545 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74706, d82545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74706, d82545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d57572 q = 1) (hb : d74711 q = 1) : d82550 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74711, d82550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74711, d82550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9222 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3931 q ha hb
  have h19 (q : Pattern) (ha : d57572 q = 1) (hb : d74712 q = 1) : d82551 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74712, d82551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74712, d82551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d57572 q = 1) (hb : d74713 q = 1) : d82552 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74713, d82552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74713, d82552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d57572 q = 1) (hb : d74714 q = 1) : d82553 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74714, d82553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74714, d82553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d57572 q = 1) (hb : d74715 q = 1) : d82554 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74715, d82554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74715, d82554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d57572 q = 1) (hb : d74716 q = 1) : d82555 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74716, d82555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74716, d82555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro9224 (p : Pattern) (ha : d57572 p = 1) (hb : d74722 p = 1) : d82561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57572 q = 1) (hb : d74717 q = 1) : d82556 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74717, d82556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74717, d82556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9223 q ha hb
  have h2 (q : Pattern) (ha : d57572 q = 1) (hb : d74718 q = 1) : d82557 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74718, d82557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74718, d82557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74719 q = 1) : d82558 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74719, d82558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74719, d82558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57572 q = 1) (hb : d74720 q = 1) : d82559 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74720, d82559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74720, d82559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57572 q = 1) (hb : d74721 q = 1) : d82560 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74721, d82560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74721, d82560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74722 q = 1) : d82561 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74722, d82561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74722, d82561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9225 (p : Pattern) (ha : d57572 p = 1) (hb : d74729 p = 1) : d82568 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1648 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1649 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1649, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1650 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1658 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1659 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1659, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4525 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d5650 q = 1) : d5650 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d57572 q = 1) (hb : d74726 q = 1) : d82565 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74726, d82565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d57572, d74726, d82565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d57572 q = 1) (hb : d74727 q = 1) : d82566 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74727, d82566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d74727, d82566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d57572 q = 1) (hb : d74728 q = 1) : d82567 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74728, d82567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74728, d82567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d57572 q = 1) (hb : d74729 q = 1) : d82568 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74729, d82568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74729, d82568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro9226 (p : Pattern) (ha : d57572 p = 1) (hb : d74733 p = 1) : d82572 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1648 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1649 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1649, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1650 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1658 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1659 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d1659, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4525 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d5650 q = 1) : d5650 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d57572 q = 1) (hb : d74726 q = 1) : d82565 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74726, d82565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d57572, d74726, d82565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d57572 q = 1) (hb : d74727 q = 1) : d82566 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74727, d82566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d74727, d82566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d57572 q = 1) (hb : d74728 q = 1) : d82567 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74728, d82567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74728, d82567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d1806 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1807 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1807, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d1807, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d1808 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d1812 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d1813 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1813, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d1813, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d4530 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d5657 q = 1) : d5657 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d57572 q = 1) (hb : d74730 q = 1) : d82569 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74730, d82569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d57572, d74730, d82569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d57572 q = 1) (hb : d74731 q = 1) : d82570 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74731, d82570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d74731, d82570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d57572 q = 1) (hb : d74732 q = 1) : d82571 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74732, d82571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d74732, d82571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d57572 q = 1) (hb : d74733 q = 1) : d82572 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74733, d82572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74733, d82572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro9227 (p : Pattern) (ha : d57572 p = 1) (hb : d74740 p = 1) : d82577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4530 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d5657 q = 1) : d5657 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74730 q = 1) : d82569 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74730, d82569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57572, d74730, d82569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57572 q = 1) (hb : d74738 q = 1) : d82570 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74738, d82570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74738, d82570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57572 q = 1) (hb : d74739 q = 1) : d82571 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74739, d82571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74739, d82571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74740 q = 1) : d82577 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74740, d82577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74740, d82577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9228 (p : Pattern) (ha : d57572 p = 1) (hb : d74749 p = 1) : d82586 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4545 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d5694 q = 1) : d5694 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74746 q = 1) : d82583 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74746, d82583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57572, d74746, d82583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57572 q = 1) (hb : d74747 q = 1) : d82584 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74747, d82584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74747, d82584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57572 q = 1) (hb : d74748 q = 1) : d82585 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74748, d82585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74748, d82585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74749 q = 1) : d82586 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74749, d82586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74749, d82586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9229 (p : Pattern) (ha : d57572 p = 1) (hb : d74755 p = 1) : d82592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3938 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3938 q ha hb
    | true =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3939 q ha hb
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1642 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74734 q = 1) : d82573 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74734, d82573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9225 q ha hb
    | true =>
      simp only [d74734, d82573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9226 q ha hb
  have h7 (q : Pattern) (ha : d1839 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3940 q ha hb
    | true =>
      simp only [d1839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3941 q ha hb
  have h8 (q : Pattern) (ha : d57572 q = 1) (hb : d74735 q = 1) : d82574 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74735, d82574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74735, d82574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d57572 q = 1) (hb : d74736 q = 1) : d82575 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74736, d82575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74736, d82575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d57572 q = 1) (hb : d74737 q = 1) : d82576 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74737, d82576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d74737, d82576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d57572 q = 1) (hb : d74741 q = 1) : d82578 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74741, d82578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74741, d82578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9227 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3942 q ha hb
  have h13 (q : Pattern) (ha : d57572 q = 1) (hb : d74742 q = 1) : d82579 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74742, d82579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74742, d82579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d57572 q = 1) (hb : d74743 q = 1) : d82580 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74743, d82580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74743, d82580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d57572 q = 1) (hb : d74744 q = 1) : d82581 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74744, d82581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74744, d82581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d57572 q = 1) (hb : d74745 q = 1) : d82582 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74745, d82582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74745, d82582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d57572 q = 1) (hb : d74750 q = 1) : d82587 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74750, d82587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74750, d82587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9228 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3943 q ha hb
  have h19 (q : Pattern) (ha : d57572 q = 1) (hb : d74751 q = 1) : d82588 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74751, d82588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74751, d82588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d57572 q = 1) (hb : d74752 q = 1) : d82589 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74752, d82589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74752, d82589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d57572 q = 1) (hb : d74753 q = 1) : d82590 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74753, d82590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74753, d82590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d57572 q = 1) (hb : d74754 q = 1) : d82591 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74754, d82591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74754, d82591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d57572 q = 1) (hb : d74755 q = 1) : d82592 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74755, d82592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74755, d82592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro9230 (p : Pattern) (ha : d57572 p = 1) (hb : d74761 p = 1) : d82598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57572 q = 1) (hb : d74756 q = 1) : d82593 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74756, d82593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74756, d82593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9229 q ha hb
  have h2 (q : Pattern) (ha : d57572 q = 1) (hb : d74757 q = 1) : d82594 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74757, d82594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74757, d82594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74758 q = 1) : d82595 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74758, d82595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74758, d82595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57572 q = 1) (hb : d74759 q = 1) : d82596 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74759, d82596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74759, d82596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57572 q = 1) (hb : d74760 q = 1) : d82597 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74760, d82597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74760, d82597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74761 q = 1) : d82598 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74761, d82598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74761, d82598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9231 (p : Pattern) (ha : d57572 p = 1) (hb : d74769 p = 1) : d82606 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2131 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2132 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2132, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2133 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2141 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2142 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d2142, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4566 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d5741 q = 1) : d5741 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d57572 q = 1) (hb : d74766 q = 1) : d82603 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74766, d82603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d57572, d74766, d82603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d57572 q = 1) (hb : d74767 q = 1) : d82604 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74767, d82604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d74767, d82604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d57572 q = 1) (hb : d74768 q = 1) : d82605 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74768, d82605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74768, d82605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d57572 q = 1) (hb : d74769 q = 1) : d82606 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74769, d82606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74769, d82606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro9232 (p : Pattern) (ha : d57572 p = 1) (hb : d74773 p = 1) : d82610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2131 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2132 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2132, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2133 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2141 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2142 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d2142, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d4566 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d5741 q = 1) : d5741 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d57572 q = 1) (hb : d74766 q = 1) : d82603 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74766, d82603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d57572, d74766, d82603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d57572 q = 1) (hb : d74767 q = 1) : d82604 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74767, d82604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d74767, d82604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d57572 q = 1) (hb : d74768 q = 1) : d82605 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74768, d82605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74768, d82605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d2284 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d2285 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2285, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d2285, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d2286 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d2290 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d2291 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2291, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d2291, d57572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d4571 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d1 q = 1) (hb : d5748 q = 1) : d5748 q = 1 := by
    exact hb
  have h19 (q : Pattern) (ha : d57572 q = 1) (hb : d74770 q = 1) : d82607 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74770, d82607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d57572, d74770, d82607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d57572 q = 1) (hb : d74771 q = 1) : d82608 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74771, d82608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d74771, d82608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d57572 q = 1) (hb : d74772 q = 1) : d82609 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74772, d82609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d74772, d82609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d57572 q = 1) (hb : d74773 q = 1) : d82610 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74773, d82610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74773, d82610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro9233 (p : Pattern) (ha : d57572 p = 1) (hb : d74780 p = 1) : d82615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4571 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d5748 q = 1) : d5748 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74770 q = 1) : d82607 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74770, d82607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57572, d74770, d82607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57572 q = 1) (hb : d74778 q = 1) : d82608 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74778, d82608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74778, d82608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57572 q = 1) (hb : d74779 q = 1) : d82609 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74779, d82609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74779, d82609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74780 q = 1) : d82615 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74780, d82615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74780, d82615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9234 (p : Pattern) (ha : d57572 p = 1) (hb : d74789 p = 1) : d82624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4586 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d5785 q = 1) : d5785 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74786 q = 1) : d82621 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d57572, d74786, d82621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57572, d74786, d82621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57572 q = 1) (hb : d74787 q = 1) : d82622 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74787, d82622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74787, d82622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57572 q = 1) (hb : d74788 q = 1) : d82623 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74788, d82623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74788, d82623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74789 q = 1) : d82624 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74789, d82624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74789, d82624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9235 (p : Pattern) (ha : d57572 p = 1) (hb : d74795 p = 1) : d82630 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3950 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3950 q ha hb
    | true =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3951 q ha hb
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2125 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74774 q = 1) : d82611 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74774, d82611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9231 q ha hb
    | true =>
      simp only [d74774, d82611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9232 q ha hb
  have h7 (q : Pattern) (ha : d2317 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3952 q ha hb
    | true =>
      simp only [d2317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3953 q ha hb
  have h8 (q : Pattern) (ha : d57572 q = 1) (hb : d74775 q = 1) : d82612 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74775, d82612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74775, d82612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d57572 q = 1) (hb : d74776 q = 1) : d82613 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74776, d82613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74776, d82613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d57572 q = 1) (hb : d74777 q = 1) : d82614 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74777, d82614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d74777, d82614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d57572 q = 1) (hb : d74781 q = 1) : d82616 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74781, d82616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74781, d82616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9233 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3954 q ha hb
  have h13 (q : Pattern) (ha : d57572 q = 1) (hb : d74782 q = 1) : d82617 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74782, d82617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74782, d82617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d57572 q = 1) (hb : d74783 q = 1) : d82618 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74783, d82618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74783, d82618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d57572 q = 1) (hb : d74784 q = 1) : d82619 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74784, d82619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74784, d82619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d57572 q = 1) (hb : d74785 q = 1) : d82620 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74785, d82620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74785, d82620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d57572 q = 1) (hb : d74790 q = 1) : d82625 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74790, d82625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74790, d82625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9234 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3955 q ha hb
  have h19 (q : Pattern) (ha : d57572 q = 1) (hb : d74791 q = 1) : d82626 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74791, d82626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74791, d82626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d57572 q = 1) (hb : d74792 q = 1) : d82627 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74792, d82627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74792, d82627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d57572 q = 1) (hb : d74793 q = 1) : d82628 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74793, d82628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74793, d82628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d57572 q = 1) (hb : d74794 q = 1) : d82629 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74794, d82629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74794, d82629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d57572 q = 1) (hb : d74795 q = 1) : d82630 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74795, d82630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74795, d82630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro9236 (p : Pattern) (ha : d57572 p = 1) (hb : d74801 p = 1) : d82636 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57572 q = 1) (hb : d74796 q = 1) : d82631 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74796, d82631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74796, d82631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9235 q ha hb
  have h2 (q : Pattern) (ha : d57572 q = 1) (hb : d74797 q = 1) : d82632 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74797, d82632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74797, d82632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74798 q = 1) : d82633 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74798, d82633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74798, d82633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57572 q = 1) (hb : d74799 q = 1) : d82634 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74799, d82634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74799, d82634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d57572 q = 1) (hb : d74800 q = 1) : d82635 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74800, d82635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74800, d82635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74801 q = 1) : d82636 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74801, d82636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74801, d82636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro9237 (p : Pattern) (ha : d57572 p = 1) (hb : d74807 p = 1) : d82642 p = 1 := by
  have h0 (q : Pattern) (ha : d57572 q = 1) (hb : d74648 q = 1) : d82491 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74648, d82491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9206 q ha hb
    | true =>
      simp only [d74648, d82491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9212 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d57572 q = 1) (hb : d74685 q = 1) : d82526 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74685, d82526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74685, d82526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9218 q ha hb
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74686 q = 1) : d82527 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74686, d82527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74686, d82527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d57572 q = 1) (hb : d74723 q = 1) : d82562 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74723, d82562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74723, d82562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9224 q ha hb
  have h5 (q : Pattern) (ha : d57572 q = 1) (hb : d74724 q = 1) : d82563 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74724, d82563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74724, d82563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74725 q = 1) : d82564 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74725, d82564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74725, d82564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d57572 q = 1) (hb : d74762 q = 1) : d82599 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74762, d82599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74762, d82599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9230 q ha hb
  have h8 (q : Pattern) (ha : d57572 q = 1) (hb : d74763 q = 1) : d82600 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74763, d82600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74763, d82600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d57572 q = 1) (hb : d74764 q = 1) : d82601 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74764, d82601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74764, d82601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d57572 q = 1) (hb : d74765 q = 1) : d82602 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74765, d82602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74765, d82602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d57572 q = 1) (hb : d74802 q = 1) : d82637 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74802, d82637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74802, d82637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9236 q ha hb
  have h12 (q : Pattern) (ha : d57572 q = 1) (hb : d74803 q = 1) : d82638 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74803, d82638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74803, d82638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d57572 q = 1) (hb : d74804 q = 1) : d82639 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74804, d82639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74804, d82639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d57572 q = 1) (hb : d74805 q = 1) : d82640 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74805, d82640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74805, d82640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d57572 q = 1) (hb : d74806 q = 1) : d82641 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d74806, d82641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74806, d82641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d57572 q = 1) (hb : d74807 q = 1) : d82642 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d74807, d82642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74807, d82642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro9238 (p : Pattern) (ha : d57572 p = 1) (hb : d74813 p = 1) : d82648 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57572 q = 1) (hb : d74808 q = 1) : d82643 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d74808, d82643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9237 q ha hb
    | true =>
      simp only [d74808, d82643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d57572 q = 1) (hb : d74809 q = 1) : d82644 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d74809, d82644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74809, d82644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74810 q = 1) : d82645 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d74810, d82645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74810, d82645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d57572 q = 1) (hb : d74811 q = 1) : d82646 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d74811, d82646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74811, d82646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d57572 q = 1) (hb : d74812 q = 1) : d82647 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d74812, d82647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74812, d82647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74813 q = 1) : d82648 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d74813, d82648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74813, d82648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro9239 (p : Pattern) (ha : d57572 p = 1) (hb : d74819 p = 1) : d82654 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57572 q = 1) (hb : d74814 q = 1) : d82649 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d74814, d82649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9238 q ha hb
    | true =>
      simp only [d74814, d82649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d57572 q = 1) (hb : d74815 q = 1) : d82650 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d74815, d82650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74815, d82650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74816 q = 1) : d82651 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d74816, d82651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74816, d82651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d57572 q = 1) (hb : d74817 q = 1) : d82652 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d74817, d82652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74817, d82652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d57572 q = 1) (hb : d74818 q = 1) : d82653 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d74818, d82653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74818, d82653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74819 q = 1) : d82654 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d74819, d82654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74819, d82654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro9240 (p : Pattern) (ha : d57572 p = 1) (hb : d74825 p = 1) : d82660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57572 q = 1) (hb : d74820 q = 1) : d82655 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d74820, d82655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9239 q ha hb
    | true =>
      simp only [d74820, d82655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d57572 q = 1) (hb : d74821 q = 1) : d82656 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d74821, d82656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74821, d82656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74822 q = 1) : d82657 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d74822, d82657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74822, d82657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d57572 q = 1) (hb : d74823 q = 1) : d82658 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d74823, d82658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74823, d82658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d57572 q = 1) (hb : d74824 q = 1) : d82659 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d74824, d82659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74824, d82659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74825 q = 1) : d82660 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d74825, d82660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74825, d82660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro9241 (p : Pattern) (ha : d57572 p = 1) (hb : d74831 p = 1) : d82666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57572 q = 1) (hb : d74826 q = 1) : d82661 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d74826, d82661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9240 q ha hb
    | true =>
      simp only [d74826, d82661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d57572 q = 1) (hb : d74827 q = 1) : d82662 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d74827, d82662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74827, d82662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74828 q = 1) : d82663 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d74828, d82663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74828, d82663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d57572 q = 1) (hb : d74829 q = 1) : d82664 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d74829, d82664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74829, d82664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d57572 q = 1) (hb : d74830 q = 1) : d82665 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d74830, d82665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74830, d82665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d57572 q = 1) (hb : d74831 q = 1) : d82666 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d74831, d82666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74831, d82666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro9242 (p : Pattern) (ha : d67923 p = 1) (hb : d74837 p = 1) : d82672 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d57572 q = 1) (hb : d74832 q = 1) : d82667 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d74832, d82667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9241 q ha hb
    | true =>
      simp only [d74832, d82667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d57572 q = 1) (hb : d74833 q = 1) : d82668 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d74833, d82668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74833, d82668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d57572 q = 1) (hb : d74834 q = 1) : d82669 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d74834, d82669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74834, d82669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d67923 q = 1) (hb : d74835 q = 1) : d82670 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d67923, d74835, d82670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d67923, d74835, d82670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d67923 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d67923 q = 1) (hb : d74836 q = 1) : d82671 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74836, d82671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74836, d82671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d67923 q = 1) (hb : d74837 q = 1) : d82672 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d74837, d82672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74837, d82672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h8 p ha hb
theorem andIntro9243 (p : Pattern) (ha : d67924 p = 1) (hb : d74843 p = 1) : d82678 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d67923 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67923 q = 1) (hb : d74838 q = 1) : d82673 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74838, d82673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9242 q ha hb
    | true =>
      simp only [d74838, d82673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d67923 q = 1) (hb : d74839 q = 1) : d82674 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74839, d82674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74839, d82674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67924 q = 1) (hb : d74840 q = 1) : d82675 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d67924, d74840, d82675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67924, d74840, d82675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d67924 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d67924 q = 1) (hb : d74841 q = 1) : d82676 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74841, d82676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74841, d82676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d67924 q = 1) (hb : d74842 q = 1) : d82677 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74842, d82677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74842, d82677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h8 (q : Pattern) (ha : d67924 q = 1) (hb : d74843 q = 1) : d82678 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d74843, d82678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74843, d82678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h8 p ha hb
theorem andIntro9244 (p : Pattern) (ha : d67924 p = 1) (hb : d74849 p = 1) : d82684 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d67924 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d67924 q = 1) (hb : d74844 q = 1) : d82679 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74844, d82679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9243 q ha hb
    | true =>
      simp only [d74844, d82679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d67924 q = 1) (hb : d74845 q = 1) : d82680 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74845, d82680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74845, d82680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d67924 q = 1) (hb : d74846 q = 1) : d82681 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74846, d82681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74846, d82681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d67924 q = 1) (hb : d74847 q = 1) : d82682 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74847, d82682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74847, d82682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d67924 q = 1) (hb : d74848 q = 1) : d82683 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74848, d82683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74848, d82683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d67924 q = 1) (hb : d74849 q = 1) : d82684 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d74849, d82684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74849, d82684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro9245 (p : Pattern) (ha : d1 p = 1) (hb : d82684 p = 1) : d82684 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d82684 q = 1) : d82684 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro9246 (p : Pattern) (ha : d74849 p = 1) (hb : d82685 p = 1) : d74849 p = 1 := by
  have h0 (q : Pattern) (ha : d74849 q = 1) (hb : d82685 q = 1) : d74849 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro9247 (p : Pattern) (ha : d74080 p = 1) (hb : d74579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d297 q = 1) (hb : d52096 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51 q ha hb
    | true =>
      simp only [d297, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d298 q = 1) (hb : d52097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d299 q = 1) (hb : d52098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d299, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d300 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d304 q = 1) (hb : d52103 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52 q ha hb
    | true =>
      simp only [d304, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d305 q = 1) (hb : d52104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d337 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53 q ha hb
    | true =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4371 q = 1) (hb : d52137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4371, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4737 q = 1) (hb : d68836 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7493 q ha hb
    | true =>
      simp only [d4737, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5350 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5350, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74077 q = 1) (hb : d74576 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74077, d74576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d74077, d74576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74078 q = 1) (hb : d74577 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74078, d74577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74078, d74577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74079 q = 1) (hb : d74578 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74079, d74578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74079, d74578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74080 q = 1) (hb : d74579 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74080, d74579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74080, d74579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro9248 (p : Pattern) (ha : d74087 p = 1) (hb : d74583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d297 q = 1) (hb : d52096 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro51 q ha hb
    | true =>
      simp only [d297, d52096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d298 q = 1) (hb : d52097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d52097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d299 q = 1) (hb : d52098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d299, d52098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d300 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d52099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d304 q = 1) (hb : d52103 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52 q ha hb
    | true =>
      simp only [d304, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d305 q = 1) (hb : d52104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d337 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53 q ha hb
    | true =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4371 q = 1) (hb : d52137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4371, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4737 q = 1) (hb : d68836 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7493 q ha hb
    | true =>
      simp only [d4737, d68836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5350 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5350, d74076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d74077 q = 1) (hb : d74576 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74077, d74576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d74077, d74576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d74078 q = 1) (hb : d74577 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74078, d74577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d74078, d74577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74079 q = 1) (hb : d74578 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74079, d74578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74079, d74578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d377 q = 1) (hb : d52145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d52145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro55 q ha hb
    | true =>
      simp only [d377, d52145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
  have h17 (q : Pattern) (ha : d378 q = 1) (hb : d52146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d52146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d378, d52146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d379 q = 1) (hb : d52147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d52147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d379, d52147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d380 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d52148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, d52148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d382 q = 1) (hb : d52150 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d52150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56 q ha hb
    | true =>
      simp only [d382, d52150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
  have h21 (q : Pattern) (ha : d383 q = 1) (hb : d52151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d52151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d383, d52151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d384 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d52152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d384, d52152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d386 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45 q ha hb
    | true =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d4376 q = 1) (hb : d52155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d4376, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d5356 q = 1) (hb : d74082 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7495 q ha hb
    | true =>
      simp only [d5356, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d5357 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d5357, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d74084 q = 1) (hb : d74580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74084, d74580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d74084, d74580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d74085 q = 1) (hb : d74581 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74085, d74581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d74085, d74581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d74086 q = 1) (hb : d74582 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74086, d74582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d74086, d74582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d74087 q = 1) (hb : d74583 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74087, d74583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74087, d74583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro9249 (p : Pattern) (ha : d74094 p = 1) (hb : d74590 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d386 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45 q ha hb
    | true =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4376 q = 1) (hb : d52155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4376, d52155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5356 q = 1) (hb : d74082 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7495 q ha hb
    | true =>
      simp only [d5356, d74082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5357 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5357, d74083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74084 q = 1) (hb : d74580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74084, d74580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74084, d74580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74092 q = 1) (hb : d74588 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74092, d74588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74092, d74588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74093 q = 1) (hb : d74589 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74093, d74589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74093, d74589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74094 q = 1) (hb : d74590 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74094, d74590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74094, d74590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
end NetHack.Soko22Hazard87
