import NetHack.Soko22Hazard87.AndIntroBlocks0127
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro32000 (p : Pattern) (ha : d107528 p = 1) (hb : d141338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88402 q = 1) (hb : d107523 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88402, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10566 q ha hb
    | true =>
      simp only [d88402, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d88403 q = 1) (hb : d107524 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88403, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88403, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d88404 q = 1) (hb : d107525 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88404, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88404, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107526 q = 1) (hb : d141336 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107526, d141336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d107526, d141336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d107527 q = 1) (hb : d141337 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107527, d141337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107527, d141337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107528 q = 1) (hb : d141338 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107528, d141338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107528, d141338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32001 (p : Pattern) (ha : d107534 p = 1) (hb : d141344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107529 q = 1) (hb : d141339 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107529, d141339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32000 q ha hb
    | true =>
      simp only [d107529, d141339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107530 q = 1) (hb : d141340 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107530, d141340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107530, d141340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d51930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11 q ha hb
    | true =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d51931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107531 q = 1) (hb : d141341 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107531, d141341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107531, d141341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107532 q = 1) (hb : d141342 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107532, d141342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107532, d141342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107533 q = 1) (hb : d141343 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107533, d141343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107533, d141343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107534 q = 1) (hb : d141344 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107534, d141344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107534, d141344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32002 (p : Pattern) (ha : d107540 p = 1) (hb : d141350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107535 q = 1) (hb : d141345 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107535, d141345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32001 q ha hb
    | true =>
      simp only [d107535, d141345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107536 q = 1) (hb : d141346 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107536, d141346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107536, d141346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d107537 q = 1) (hb : d141347 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107537, d141347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107537, d141347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107538 q = 1) (hb : d141348 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107538, d141348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107538, d141348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107539 q = 1) (hb : d141349 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107539, d141349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107539, d141349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107540 q = 1) (hb : d141350 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107540, d141350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107540, d141350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32003 (p : Pattern) (ha : d107546 p = 1) (hb : d141356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d51957 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d51958 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d51964 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
    | true =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d51965 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107511 q = 1) (hb : d141324 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107511, d141324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31996 q ha hb
    | true =>
      simp only [d107511, d141324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31998 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d107512 q = 1) (hb : d141325 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107512, d141325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107512, d141325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d107513 q = 1) (hb : d141326 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107513, d141326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107513, d141326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d107514 q = 1) (hb : d141327 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107514, d141327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d107514, d141327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107518 q = 1) (hb : d141331 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107518, d141331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107518, d141331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31999 q ha hb
  have h12 (q : Pattern) (ha : d107519 q = 1) (hb : d141332 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107519, d141332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107519, d141332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107520 q = 1) (hb : d141333 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107520, d141333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107520, d141333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d107521 q = 1) (hb : d141334 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107521, d141334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107521, d141334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d107522 q = 1) (hb : d141335 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107522, d141335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107522, d141335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107541 q = 1) (hb : d141351 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107541, d141351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107541, d141351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32002 q ha hb
  have h17 (q : Pattern) (ha : d107542 q = 1) (hb : d141352 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107542, d141352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d107542, d141352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d107543 q = 1) (hb : d141353 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107543, d141353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107543, d141353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d107544 q = 1) (hb : d141354 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107544, d141354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d107544, d141354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d107545 q = 1) (hb : d141355 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107545, d141355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d107545, d141355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d107546 q = 1) (hb : d141356 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107546, d141356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107546, d141356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro32004 (p : Pattern) (ha : d107556 p = 1) (hb : d141366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107498 q = 1) (hb : d141311 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107498, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31995 q ha hb
    | true =>
      simp only [d107498, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d107552 q = 1) (hb : d141362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107552, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107552, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107553 q = 1) (hb : d141363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107553, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107553, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107554 q = 1) (hb : d141364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107554, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107554, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107555 q = 1) (hb : d141365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107555, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107555, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107556 q = 1) (hb : d141366 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107556, d141366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107556, d141366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32005 (p : Pattern) (ha : d107563 p = 1) (hb : d141373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107498 q = 1) (hb : d141311 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107498, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31995 q ha hb
    | true =>
      simp only [d107498, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d107552 q = 1) (hb : d141362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107552, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107552, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107553 q = 1) (hb : d141363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107553, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107553, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107554 q = 1) (hb : d141364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107554, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107554, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107555 q = 1) (hb : d141365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107555, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107555, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107505 q = 1) (hb : d141318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107505, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31997 q ha hb
    | true =>
      simp only [d107505, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h7 (q : Pattern) (ha : d107559 q = 1) (hb : d141369 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107559, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107559, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107560 q = 1) (hb : d141370 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107560, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107560, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107561 q = 1) (hb : d141371 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107561, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107561, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107562 q = 1) (hb : d141372 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107562, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107562, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107563 q = 1) (hb : d141373 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107563, d141373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107563, d141373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32006 (p : Pattern) (ha : d107568 p = 1) (hb : d141378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107492 q = 1) (hb : d141305 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31994 q ha hb
    | true =>
      simp only [d107492, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107493 q = 1) (hb : d141306 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107494 q = 1) (hb : d141307 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107494, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107494, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107495 q = 1) (hb : d141308 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107495, d141308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107495, d141308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107567 q = 1) (hb : d141377 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107567, d141377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107567, d141377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107568 q = 1) (hb : d141378 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107568, d141378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107568, d141378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32007 (p : Pattern) (ha : d107575 p = 1) (hb : d141385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107492 q = 1) (hb : d141305 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31994 q ha hb
    | true =>
      simp only [d107492, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107493 q = 1) (hb : d141306 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107494 q = 1) (hb : d141307 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107494, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107494, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107573 q = 1) (hb : d141383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107573, d141383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107573, d141383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107574 q = 1) (hb : d141384 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107574, d141384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107574, d141384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107575 q = 1) (hb : d141385 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107575, d141385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107575, d141385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32008 (p : Pattern) (ha : d107584 p = 1) (hb : d141391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107579 q = 1) (hb : d114306 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107579, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22838 q hb ha
    | true =>
      simp only [d107579, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107580 q = 1) (hb : d114307 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107580, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107580, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107581 q = 1) (hb : d114308 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107581, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107581, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88338 q = 1) (hb : d107486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88338, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10549 q ha hb
    | true =>
      simp only [d88338, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88339 q = 1) (hb : d107487 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88339, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88339, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88340 q = 1) (hb : d107488 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88340, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88340, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107582 q = 1) (hb : d141389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107582, d141389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107582, d141389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107489 q = 1) (hb : d141302 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107489, d141302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d107489, d141302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d107583 q = 1) (hb : d141390 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107583, d141390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107583, d141390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107584 q = 1) (hb : d141391 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107584, d141391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107584, d141391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro32009 (p : Pattern) (ha : d107590 p = 1) (hb : d141397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107585 q = 1) (hb : d141392 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107585, d141392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32008 q ha hb
    | true =>
      simp only [d107585, d141392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107586 q = 1) (hb : d141393 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107586, d141393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107586, d141393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107492 q = 1) (hb : d141305 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31994 q ha hb
    | true =>
      simp only [d107492, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107493 q = 1) (hb : d141306 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107587 q = 1) (hb : d141394 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107587, d141394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107587, d141394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107588 q = 1) (hb : d141395 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107588, d141395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107588, d141395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107589 q = 1) (hb : d141396 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107589, d141396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107589, d141396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107590 q = 1) (hb : d141397 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107590, d141397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107590, d141397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32010 (p : Pattern) (ha : d107596 p = 1) (hb : d141403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107492 q = 1) (hb : d141305 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31994 q ha hb
    | true =>
      simp only [d107492, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107493 q = 1) (hb : d141306 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107593 q = 1) (hb : d141400 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107593, d141400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107593, d141400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107594 q = 1) (hb : d141401 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107594, d141401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107594, d141401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107595 q = 1) (hb : d141402 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107595, d141402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107595, d141402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107596 q = 1) (hb : d141403 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107596, d141403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107596, d141403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32011 (p : Pattern) (ha : d107602 p = 1) (hb : d141409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107569 q = 1) (hb : d141379 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107569, d141379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32006 q ha hb
    | true =>
      simp only [d107569, d141379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d107570 q = 1) (hb : d141380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107570, d141380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107570, d141380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107571 q = 1) (hb : d141381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107571, d141381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107571, d141381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107572 q = 1) (hb : d141382 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107572, d141382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107572, d141382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107576 q = 1) (hb : d141386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107576, d141386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32007 q ha hb
    | true =>
      simp only [d107576, d141386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d107577 q = 1) (hb : d141387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107577, d141387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107577, d141387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107578 q = 1) (hb : d141388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107578, d141388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107578, d141388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107591 q = 1) (hb : d141398 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107591, d141398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32009 q ha hb
    | true =>
      simp only [d107591, d141398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31995 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107498 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107592 q = 1) (hb : d141399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107592, d141399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107592, d141399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d107597 q = 1) (hb : d141404 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107597, d141404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32010 q ha hb
    | true =>
      simp only [d107597, d141404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107598 q = 1) (hb : d141405 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107598, d141405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107598, d141405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107599 q = 1) (hb : d141406 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107599, d141406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107599, d141406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107600 q = 1) (hb : d141407 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107600, d141407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107600, d141407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107601 q = 1) (hb : d141408 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107601, d141408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107601, d141408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107602 q = 1) (hb : d141409 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107602, d141409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107602, d141409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro32012 (p : Pattern) (ha : d107603 p = 1) (hb : d141410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107492 q = 1) (hb : d141305 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31994 q ha hb
    | true =>
      simp only [d107492, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107493 q = 1) (hb : d141306 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107494 q = 1) (hb : d141307 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107494, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107494, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107495 q = 1) (hb : d141308 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107495, d141308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107495, d141308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107567 q = 1) (hb : d141377 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107567, d141377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107567, d141377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107603 q = 1) (hb : d141410 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107603, d141410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107603, d141410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32013 (p : Pattern) (ha : d107608 p = 1) (hb : d141415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107492 q = 1) (hb : d141305 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31994 q ha hb
    | true =>
      simp only [d107492, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107493 q = 1) (hb : d141306 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107494 q = 1) (hb : d141307 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107494, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107494, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d107573 q = 1) (hb : d141383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107573, d141383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107573, d141383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107574 q = 1) (hb : d141384 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107574, d141384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107574, d141384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107608 q = 1) (hb : d141415 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107608, d141415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107608, d141415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32014 (p : Pattern) (ha : d107612 p = 1) (hb : d141419 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107585 q = 1) (hb : d141392 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107585, d141392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32008 q ha hb
    | true =>
      simp only [d107585, d141392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107586 q = 1) (hb : d141393 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107586, d141393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107586, d141393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107492 q = 1) (hb : d141305 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31994 q ha hb
    | true =>
      simp only [d107492, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107493 q = 1) (hb : d141306 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107587 q = 1) (hb : d141394 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107587, d141394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107587, d141394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107588 q = 1) (hb : d141395 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107588, d141395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107588, d141395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107589 q = 1) (hb : d141396 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107589, d141396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107589, d141396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107612 q = 1) (hb : d141419 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107612, d141419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107612, d141419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32015 (p : Pattern) (ha : d107615 p = 1) (hb : d141422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107492 q = 1) (hb : d141305 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107492, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31994 q ha hb
    | true =>
      simp only [d107492, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107493 q = 1) (hb : d141306 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107493, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107493, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107593 q = 1) (hb : d141400 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107593, d141400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107593, d141400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107594 q = 1) (hb : d141401 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107594, d141401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107594, d141401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107595 q = 1) (hb : d141402 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107595, d141402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107595, d141402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107615 q = 1) (hb : d141422 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107615, d141422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107615, d141422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32016 (p : Pattern) (ha : d107621 p = 1) (hb : d141428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107569 q = 1) (hb : d141379 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107569, d141379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32006 q ha hb
    | true =>
      simp only [d107569, d141379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d107570 q = 1) (hb : d141380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107570, d141380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107570, d141380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107571 q = 1) (hb : d141381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107571, d141381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107571, d141381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107572 q = 1) (hb : d141382 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107572, d141382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107572, d141382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107576 q = 1) (hb : d141386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107576, d141386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32007 q ha hb
    | true =>
      simp only [d107576, d141386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d107577 q = 1) (hb : d141387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107577, d141387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107577, d141387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107578 q = 1) (hb : d141388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107578, d141388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107578, d141388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107591 q = 1) (hb : d141398 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107591, d141398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32009 q ha hb
    | true =>
      simp only [d107591, d141398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31995 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107498 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107592 q = 1) (hb : d141399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107592, d141399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107592, d141399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d107597 q = 1) (hb : d141404 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107597, d141404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32010 q ha hb
    | true =>
      simp only [d107597, d141404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107598 q = 1) (hb : d141405 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107598, d141405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107598, d141405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107599 q = 1) (hb : d141406 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107599, d141406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107599, d141406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107600 q = 1) (hb : d141407 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107600, d141407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107600, d141407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107601 q = 1) (hb : d141408 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107601, d141408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107601, d141408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107604 q = 1) (hb : d141411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107604, d141411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32012 q ha hb
    | true =>
      simp only [d107604, d141411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q hb ha
  have h17 (q : Pattern) (ha : d107605 q = 1) (hb : d141412 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107605, d141412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107605, d141412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107606 q = 1) (hb : d141413 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107606, d141413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107606, d141413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d107607 q = 1) (hb : d141414 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107607, d141414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107607, d141414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d107609 q = 1) (hb : d141416 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107609, d141416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32013 q ha hb
    | true =>
      simp only [d107609, d141416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q hb ha
  have h21 (q : Pattern) (ha : d107610 q = 1) (hb : d141417 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107610, d141417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107610, d141417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d107611 q = 1) (hb : d141418 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107611, d141418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d107611, d141418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107613 q = 1) (hb : d141420 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107613, d141420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32014 q ha hb
    | true =>
      simp only [d107613, d141420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31997 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d107505 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d107614 q = 1) (hb : d141421 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107614, d141421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d107614, d141421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d107616 q = 1) (hb : d141423 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107616, d141423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32015 q ha hb
    | true =>
      simp only [d107616, d141423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d107617 q = 1) (hb : d141424 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107617, d141424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d107617, d141424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d107618 q = 1) (hb : d141425 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107618, d141425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d107618, d141425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d107619 q = 1) (hb : d141426 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107619, d141426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d107619, d141426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d107620 q = 1) (hb : d141427 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107620, d141427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d107620, d141427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d107621 q = 1) (hb : d141428 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107621, d141428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107621, d141428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro32017 (p : Pattern) (ha : d107623 p = 1) (hb : d141430 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107498 q = 1) (hb : d141311 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107498, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31995 q ha hb
    | true =>
      simp only [d107498, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d107552 q = 1) (hb : d141362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107552, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107552, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107553 q = 1) (hb : d141363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107553, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107553, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107554 q = 1) (hb : d141364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107554, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107554, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107555 q = 1) (hb : d141365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107555, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107555, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d51952 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d51953 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d51954 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d51955 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107623 q = 1) (hb : d141430 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107623, d141430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107623, d141430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro32018 (p : Pattern) (ha : d107630 p = 1) (hb : d141437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107613 q = 1) (hb : d141420 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107613, d141420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32014 q ha hb
    | true =>
      simp only [d107613, d141420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31997 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107505 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107614 q = 1) (hb : d141421 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107614, d141421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107614, d141421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d107616 q = 1) (hb : d141423 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107616, d141423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32015 q ha hb
    | true =>
      simp only [d107616, d141423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107617 q = 1) (hb : d141424 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107617, d141424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107617, d141424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107618 q = 1) (hb : d141425 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107618, d141425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107618, d141425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107628 q = 1) (hb : d141435 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107628, d141435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107628, d141435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107629 q = 1) (hb : d141436 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107629, d141436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107629, d141436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107630 q = 1) (hb : d141437 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107630, d141437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107630, d141437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32019 (p : Pattern) (ha : d107641 p = 1) (hb : d141445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107636 q = 1) (hb : d114363 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107636, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22850 q hb ha
    | true =>
      simp only [d107636, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107637 q = 1) (hb : d114364 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107637, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107637, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107638 q = 1) (hb : d114365 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107638, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107638, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88402 q = 1) (hb : d107523 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88402, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10566 q ha hb
    | true =>
      simp only [d88402, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88403 q = 1) (hb : d107524 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88403, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88403, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88404 q = 1) (hb : d107525 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88404, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88404, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107639 q = 1) (hb : d141443 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107639, d141443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107639, d141443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107526 q = 1) (hb : d141336 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107526, d141336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d107526, d141336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d107640 q = 1) (hb : d141444 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107640, d141444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107640, d141444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107641 q = 1) (hb : d141445 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107641, d141445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107641, d141445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro32020 (p : Pattern) (ha : d107647 p = 1) (hb : d141451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107642 q = 1) (hb : d141446 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107642, d141446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32019 q ha hb
    | true =>
      simp only [d107642, d141446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107643 q = 1) (hb : d141447 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107643, d141447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107643, d141447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107529 q = 1) (hb : d141339 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107529, d141339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32000 q ha hb
    | true =>
      simp only [d107529, d141339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107530 q = 1) (hb : d141340 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107530, d141340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107530, d141340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107644 q = 1) (hb : d141448 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107644, d141448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107644, d141448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107645 q = 1) (hb : d141449 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107645, d141449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107645, d141449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107646 q = 1) (hb : d141450 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107646, d141450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107646, d141450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107647 q = 1) (hb : d141451 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107647, d141451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107647, d141451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32021 (p : Pattern) (ha : d107653 p = 1) (hb : d141457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107529 q = 1) (hb : d141339 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107529, d141339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32000 q ha hb
    | true =>
      simp only [d107529, d141339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107530 q = 1) (hb : d141340 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107530, d141340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107530, d141340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107650 q = 1) (hb : d141454 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107650, d141454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107650, d141454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107651 q = 1) (hb : d141455 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107651, d141455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107651, d141455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107652 q = 1) (hb : d141456 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107652, d141456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107652, d141456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107653 q = 1) (hb : d141457 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107653, d141457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107653, d141457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32022 (p : Pattern) (ha : d107659 p = 1) (hb : d141463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107648 q = 1) (hb : d141452 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107648, d141452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32020 q ha hb
    | true =>
      simp only [d107648, d141452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32001 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107535 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107649 q = 1) (hb : d141453 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107649, d141453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107649, d141453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d107654 q = 1) (hb : d141458 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107654, d141458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32021 q ha hb
    | true =>
      simp only [d107654, d141458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107655 q = 1) (hb : d141459 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107655, d141459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107655, d141459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107656 q = 1) (hb : d141460 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107656, d141460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107656, d141460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107657 q = 1) (hb : d141461 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107657, d141461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107657, d141461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107658 q = 1) (hb : d141462 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107658, d141462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107658, d141462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107659 q = 1) (hb : d141463 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107659, d141463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107659, d141463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32023 (p : Pattern) (ha : d107665 p = 1) (hb : d141469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107557 q = 1) (hb : d141367 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107557, d141367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107557, d141367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32004 q ha hb
  have h2 (q : Pattern) (ha : d107558 q = 1) (hb : d141368 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107558, d141368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107558, d141368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107564 q = 1) (hb : d141374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107564, d141374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32004 q ha hb
    | true =>
      simp only [d107564, d141374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32005 q ha hb
  have h4 (q : Pattern) (ha : d107565 q = 1) (hb : d141375 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107565, d141375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107565, d141375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107566 q = 1) (hb : d141376 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107566, d141376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107566, d141376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107622 q = 1) (hb : d141429 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107622, d141429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32011 q ha hb
    | true =>
      simp only [d107622, d141429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32016 q ha hb
  have h7 (q : Pattern) (ha : d107624 q = 1) (hb : d141431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107624, d141431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32017 q ha hb
    | true =>
      simp only [d107624, d141431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q hb ha
  have h8 (q : Pattern) (ha : d107625 q = 1) (hb : d141432 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107625, d141432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107625, d141432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107626 q = 1) (hb : d141433 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107626, d141433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107626, d141433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d107627 q = 1) (hb : d141434 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107627, d141434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107627, d141434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107631 q = 1) (hb : d141438 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107631, d141438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107631, d141438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32018 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39 q ha hb
  have h13 (q : Pattern) (ha : d107632 q = 1) (hb : d141439 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107632, d141439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107632, d141439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d107633 q = 1) (hb : d141440 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107633, d141440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107633, d141440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d107634 q = 1) (hb : d141441 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107634, d141441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d107634, d141441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d107635 q = 1) (hb : d141442 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107635, d141442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107635, d141442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107660 q = 1) (hb : d141464 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107660, d141464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107660, d141464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32022 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40 q ha hb
  have h19 (q : Pattern) (ha : d107661 q = 1) (hb : d141465 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107661, d141465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107661, d141465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d107662 q = 1) (hb : d141466 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107662, d141466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d107662, d141466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d107663 q = 1) (hb : d141467 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107663, d141467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d107663, d141467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d107664 q = 1) (hb : d141468 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107664, d141468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d107664, d141468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107665 q = 1) (hb : d141469 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107665, d141469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d107665, d141469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro32024 (p : Pattern) (ha : d107671 p = 1) (hb : d141475 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d51948 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d51949 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d51950 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107547 q = 1) (hb : d141357 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107547, d141357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107547, d141357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32003 q ha hb
  have h6 (q : Pattern) (ha : d107548 q = 1) (hb : d141358 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107548, d141358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107548, d141358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107549 q = 1) (hb : d141359 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107549, d141359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107549, d141359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107550 q = 1) (hb : d141360 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107550, d141360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107550, d141360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107551 q = 1) (hb : d141361 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107551, d141361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107551, d141361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107666 q = 1) (hb : d141470 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107666, d141470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107666, d141470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32023 q ha hb
  have h11 (q : Pattern) (ha : d107667 q = 1) (hb : d141471 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107667, d141471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107667, d141471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107668 q = 1) (hb : d141472 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107668, d141472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107668, d141472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107669 q = 1) (hb : d141473 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107669, d141473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107669, d141473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107670 q = 1) (hb : d141474 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107670, d141474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107670, d141474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107671 q = 1) (hb : d141475 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d107671, d141475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107671, d141475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32025 (p : Pattern) (ha : d107674 p = 1) (hb : d141477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107579 q = 1) (hb : d114306 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107579, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22838 q hb ha
    | true =>
      simp only [d107579, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107580 q = 1) (hb : d114307 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107580, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107580, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107581 q = 1) (hb : d114308 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107581, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107581, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88338 q = 1) (hb : d107486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88338, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10549 q ha hb
    | true =>
      simp only [d88338, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88339 q = 1) (hb : d107487 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88339, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88339, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88340 q = 1) (hb : d107488 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88340, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88340, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107582 q = 1) (hb : d141389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107582, d141389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107582, d141389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d88341 q = 1) (hb : d107672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88341, d107672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d88341, d107672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d107673 q = 1) (hb : d141476 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107673, d141476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107673, d141476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107674 q = 1) (hb : d141477 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107674, d141477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107674, d141477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32026 (p : Pattern) (ha : d107678 p = 1) (hb : d141481 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88338 q = 1) (hb : d107486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88338, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10549 q ha hb
    | true =>
      simp only [d88338, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d88339 q = 1) (hb : d107487 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88339, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88339, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d88340 q = 1) (hb : d107488 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88340, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88340, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88341 q = 1) (hb : d107672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88341, d107672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88341, d107672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d107677 q = 1) (hb : d141480 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107677, d141480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107677, d141480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107678 q = 1) (hb : d141481 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107678, d141481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107678, d141481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32027 (p : Pattern) (ha : d107684 p = 1) (hb : d141487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d141478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32025 q ha hb
    | true =>
      simp only [d107675, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d141479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107679 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32026 q ha hb
    | true =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107680 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107681 q = 1) (hb : d141484 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107681, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107681, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107682 q = 1) (hb : d141485 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107682, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107682, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107683 q = 1) (hb : d141486 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107683, d141486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107683, d141486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107684 q = 1) (hb : d141487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107684, d141487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107684, d141487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32028 (p : Pattern) (ha : d107688 p = 1) (hb : d141491 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107679 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32026 q ha hb
    | true =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107680 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107685 q = 1) (hb : d141488 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107685, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107685, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107686 q = 1) (hb : d141489 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107686, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107686, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107687 q = 1) (hb : d141490 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107687, d141490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107687, d141490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107688 q = 1) (hb : d141491 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107688, d141491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107688, d141491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32029 (p : Pattern) (ha : d107694 p = 1) (hb : d141497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107689 q = 1) (hb : d141492 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107689, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32027 q ha hb
    | true =>
      simp only [d107689, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32028 q ha hb
  have h2 (q : Pattern) (ha : d107690 q = 1) (hb : d141493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107690, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107690, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107691 q = 1) (hb : d141494 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107691, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107691, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107692 q = 1) (hb : d141495 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107692, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107692, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107693 q = 1) (hb : d141496 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107693, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107693, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107694 q = 1) (hb : d141497 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107694, d141497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107694, d141497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32030 (p : Pattern) (ha : d107697 p = 1) (hb : d141500 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d141478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32025 q ha hb
    | true =>
      simp only [d107675, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d141479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107679 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32026 q ha hb
    | true =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107680 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107681 q = 1) (hb : d141484 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107681, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107681, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107682 q = 1) (hb : d141485 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107682, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107682, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107683 q = 1) (hb : d141486 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107683, d141486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107683, d141486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107697 q = 1) (hb : d141500 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107697, d141500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107697, d141500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32031 (p : Pattern) (ha : d107698 p = 1) (hb : d141501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107679 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32026 q ha hb
    | true =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107680 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107685 q = 1) (hb : d141488 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107685, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107685, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107686 q = 1) (hb : d141489 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107686, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107686, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107687 q = 1) (hb : d141490 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107687, d141490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107687, d141490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107698 q = 1) (hb : d141501 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107698, d141501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107698, d141501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32032 (p : Pattern) (ha : d107704 p = 1) (hb : d141507 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107689 q = 1) (hb : d141492 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107689, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32027 q ha hb
    | true =>
      simp only [d107689, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32028 q ha hb
  have h2 (q : Pattern) (ha : d107690 q = 1) (hb : d141493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107690, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107690, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107691 q = 1) (hb : d141494 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107691, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107691, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107692 q = 1) (hb : d141495 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107692, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107692, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107693 q = 1) (hb : d141496 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107693, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107693, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107699 q = 1) (hb : d141502 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107699, d141502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32030 q ha hb
    | true =>
      simp only [d107699, d141502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32031 q ha hb
  have h7 (q : Pattern) (ha : d107700 q = 1) (hb : d141503 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107700, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107700, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107701 q = 1) (hb : d141504 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107701, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107701, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107702 q = 1) (hb : d141505 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107702, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107702, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107703 q = 1) (hb : d141506 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107703, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107703, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107704 q = 1) (hb : d141507 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107704, d141507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107704, d141507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32033 (p : Pattern) (ha : d107709 p = 1) (hb : d141512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d141478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32025 q ha hb
    | true =>
      simp only [d107675, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d141479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107679 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32026 q ha hb
    | true =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107680 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107681 q = 1) (hb : d141484 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107681, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107681, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107682 q = 1) (hb : d141485 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107682, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107682, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107708 q = 1) (hb : d141511 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107708, d141511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107708, d141511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107709 q = 1) (hb : d141512 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107709, d141512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107709, d141512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32034 (p : Pattern) (ha : d107711 p = 1) (hb : d141514 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107679 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32026 q ha hb
    | true =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107680 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107685 q = 1) (hb : d141488 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107685, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107685, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107686 q = 1) (hb : d141489 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107686, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107686, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107710 q = 1) (hb : d141513 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107710, d141513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107710, d141513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107711 q = 1) (hb : d141514 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107711, d141514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107711, d141514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32035 (p : Pattern) (ha : d107718 p = 1) (hb : d141521 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d141478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32025 q ha hb
    | true =>
      simp only [d107675, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d141479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107679 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32026 q ha hb
    | true =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107680 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107681 q = 1) (hb : d141484 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107681, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107681, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107716 q = 1) (hb : d141519 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107716, d141519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107716, d141519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107717 q = 1) (hb : d141520 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107717, d141520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107717, d141520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107718 q = 1) (hb : d141521 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107718, d141521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107718, d141521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32036 (p : Pattern) (ha : d107721 p = 1) (hb : d141524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107679 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32026 q ha hb
    | true =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107680 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107685 q = 1) (hb : d141488 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107685, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107685, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107719 q = 1) (hb : d141522 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107719, d141522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107719, d141522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107720 q = 1) (hb : d141523 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107720, d141523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107720, d141523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107721 q = 1) (hb : d141524 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107721, d141524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107721, d141524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32037 (p : Pattern) (ha : d107730 p = 1) (hb : d141530 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107725 q = 1) (hb : d114443 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107725, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28720 q hb ha
    | true =>
      simp only [d107725, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107726 q = 1) (hb : d114444 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107726, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107726, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107727 q = 1) (hb : d114445 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107727, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107727, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107579 q = 1) (hb : d114306 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107579, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22838 q hb ha
    | true =>
      simp only [d107579, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107580 q = 1) (hb : d114307 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107580, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107580, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107581 q = 1) (hb : d114308 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107581, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107581, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107728 q = 1) (hb : d141528 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107728, d141528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107728, d141528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88338 q = 1) (hb : d107486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88338, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10549 q ha hb
    | true =>
      simp only [d88338, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d88339 q = 1) (hb : d107487 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88339, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88339, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88340 q = 1) (hb : d107488 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88340, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88340, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107582 q = 1) (hb : d141389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107582, d141389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107582, d141389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d107729 q = 1) (hb : d141529 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107729, d141529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107729, d141529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107730 q = 1) (hb : d141530 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107730, d141530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107730, d141530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro32038 (p : Pattern) (ha : d107736 p = 1) (hb : d141536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107731 q = 1) (hb : d141531 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107731, d141531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32037 q ha hb
    | true =>
      simp only [d107731, d141531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107732 q = 1) (hb : d141532 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107732, d141532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107732, d141532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107675 q = 1) (hb : d141478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32025 q ha hb
    | true =>
      simp only [d107675, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107676 q = 1) (hb : d141479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107733 q = 1) (hb : d141533 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107733, d141533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107733, d141533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107734 q = 1) (hb : d141534 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107734, d141534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107734, d141534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107735 q = 1) (hb : d141535 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107735, d141535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107735, d141535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107736 q = 1) (hb : d141536 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107736, d141536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107736, d141536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32039 (p : Pattern) (ha : d107742 p = 1) (hb : d141542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d141478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32025 q ha hb
    | true =>
      simp only [d107675, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d141479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107739 q = 1) (hb : d141539 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107739, d141539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107739, d141539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107740 q = 1) (hb : d141540 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107740, d141540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107740, d141540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107741 q = 1) (hb : d141541 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107741, d141541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107741, d141541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107742 q = 1) (hb : d141542 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107742, d141542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107742, d141542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32040 (p : Pattern) (ha : d107748 p = 1) (hb : d141548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107712 q = 1) (hb : d141515 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107712, d141515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32033 q ha hb
    | true =>
      simp only [d107712, d141515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32034 q ha hb
  have h2 (q : Pattern) (ha : d107713 q = 1) (hb : d141516 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107713, d141516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107713, d141516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107714 q = 1) (hb : d141517 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107714, d141517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107714, d141517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107715 q = 1) (hb : d141518 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107715, d141518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107715, d141518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107722 q = 1) (hb : d141525 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107722, d141525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32035 q ha hb
    | true =>
      simp only [d107722, d141525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32036 q ha hb
  have h6 (q : Pattern) (ha : d107723 q = 1) (hb : d141526 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107723, d141526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107723, d141526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107724 q = 1) (hb : d141527 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107724, d141527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107724, d141527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107737 q = 1) (hb : d141537 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107737, d141537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32038 q ha hb
    | true =>
      simp only [d107737, d141537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32027 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107689 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107738 q = 1) (hb : d141538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107738, d141538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107738, d141538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d107743 q = 1) (hb : d141543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107743, d141543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32039 q ha hb
    | true =>
      simp only [d107743, d141543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107744 q = 1) (hb : d141544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107744, d141544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107744, d141544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107745 q = 1) (hb : d141545 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107745, d141545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107745, d141545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107746 q = 1) (hb : d141546 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107746, d141546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107746, d141546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107747 q = 1) (hb : d141547 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107747, d141547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107747, d141547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107748 q = 1) (hb : d141548 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107748, d141548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107748, d141548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro32041 (p : Pattern) (ha : d107749 p = 1) (hb : d141549 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d141478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32025 q ha hb
    | true =>
      simp only [d107675, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d141479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107679 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32026 q ha hb
    | true =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107680 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107681 q = 1) (hb : d141484 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107681, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107681, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107682 q = 1) (hb : d141485 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107682, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107682, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107708 q = 1) (hb : d141511 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107708, d141511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107708, d141511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107749 q = 1) (hb : d141549 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107749, d141549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107749, d141549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32042 (p : Pattern) (ha : d107750 p = 1) (hb : d141550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107679 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32026 q ha hb
    | true =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107680 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107685 q = 1) (hb : d141488 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107685, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107685, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107686 q = 1) (hb : d141489 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107686, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107686, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107710 q = 1) (hb : d141513 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107710, d141513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107710, d141513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107750 q = 1) (hb : d141550 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107750, d141550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107750, d141550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32043 (p : Pattern) (ha : d107755 p = 1) (hb : d141555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d141478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32025 q ha hb
    | true =>
      simp only [d107675, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d141479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107679 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32026 q ha hb
    | true =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107680 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107681 q = 1) (hb : d141484 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107681, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107681, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107716 q = 1) (hb : d141519 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107716, d141519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107716, d141519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107717 q = 1) (hb : d141520 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107717, d141520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107717, d141520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107755 q = 1) (hb : d141555 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107755, d141555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107755, d141555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32044 (p : Pattern) (ha : d107756 p = 1) (hb : d141556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107679 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32026 q ha hb
    | true =>
      simp only [d107679, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107680 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107680, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107685 q = 1) (hb : d141488 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107685, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107685, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107719 q = 1) (hb : d141522 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107719, d141522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107719, d141522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107720 q = 1) (hb : d141523 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107720, d141523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107720, d141523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107756 q = 1) (hb : d141556 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107756, d141556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107756, d141556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32045 (p : Pattern) (ha : d107760 p = 1) (hb : d141560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107731 q = 1) (hb : d141531 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107731, d141531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32037 q ha hb
    | true =>
      simp only [d107731, d141531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107732 q = 1) (hb : d141532 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107732, d141532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107732, d141532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107675 q = 1) (hb : d141478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32025 q ha hb
    | true =>
      simp only [d107675, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107676 q = 1) (hb : d141479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107733 q = 1) (hb : d141533 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107733, d141533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107733, d141533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107734 q = 1) (hb : d141534 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107734, d141534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107734, d141534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107735 q = 1) (hb : d141535 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107735, d141535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107735, d141535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107760 q = 1) (hb : d141560 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107760, d141560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107760, d141560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32046 (p : Pattern) (ha : d107763 p = 1) (hb : d141563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107675 q = 1) (hb : d141478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107675, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32025 q ha hb
    | true =>
      simp only [d107675, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107676 q = 1) (hb : d141479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107676, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107676, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107739 q = 1) (hb : d141539 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107739, d141539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107739, d141539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107740 q = 1) (hb : d141540 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107740, d141540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107740, d141540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107741 q = 1) (hb : d141541 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107741, d141541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107741, d141541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107763 q = 1) (hb : d141563 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107763, d141563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107763, d141563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32047 (p : Pattern) (ha : d107769 p = 1) (hb : d141569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107712 q = 1) (hb : d141515 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107712, d141515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32033 q ha hb
    | true =>
      simp only [d107712, d141515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32034 q ha hb
  have h2 (q : Pattern) (ha : d107713 q = 1) (hb : d141516 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107713, d141516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107713, d141516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107714 q = 1) (hb : d141517 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107714, d141517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107714, d141517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107715 q = 1) (hb : d141518 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107715, d141518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107715, d141518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107722 q = 1) (hb : d141525 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107722, d141525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32035 q ha hb
    | true =>
      simp only [d107722, d141525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32036 q ha hb
  have h6 (q : Pattern) (ha : d107723 q = 1) (hb : d141526 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107723, d141526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107723, d141526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107724 q = 1) (hb : d141527 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107724, d141527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107724, d141527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107737 q = 1) (hb : d141537 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107737, d141537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32038 q ha hb
    | true =>
      simp only [d107737, d141537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32027 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107689 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107738 q = 1) (hb : d141538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107738, d141538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107738, d141538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d107743 q = 1) (hb : d141543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107743, d141543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32039 q ha hb
    | true =>
      simp only [d107743, d141543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107744 q = 1) (hb : d141544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107744, d141544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107744, d141544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107745 q = 1) (hb : d141545 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107745, d141545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107745, d141545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107746 q = 1) (hb : d141546 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107746, d141546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107746, d141546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107747 q = 1) (hb : d141547 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107747, d141547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107747, d141547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107751 q = 1) (hb : d141551 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107751, d141551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32041 q ha hb
    | true =>
      simp only [d107751, d141551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32042 q ha hb
  have h17 (q : Pattern) (ha : d107752 q = 1) (hb : d141552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107752, d141552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107752, d141552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107753 q = 1) (hb : d141553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107753, d141553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107753, d141553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d107754 q = 1) (hb : d141554 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107754, d141554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107754, d141554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d107757 q = 1) (hb : d141557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107757, d141557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32043 q ha hb
    | true =>
      simp only [d107757, d141557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32044 q ha hb
  have h21 (q : Pattern) (ha : d107758 q = 1) (hb : d141558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107758, d141558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107758, d141558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d107759 q = 1) (hb : d141559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107759, d141559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d107759, d141559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107761 q = 1) (hb : d141561 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107761, d141561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32045 q ha hb
    | true =>
      simp only [d107761, d141561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32030 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d107699 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d107762 q = 1) (hb : d141562 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107762, d141562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d107762, d141562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d107764 q = 1) (hb : d141564 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107764, d141564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32046 q ha hb
    | true =>
      simp only [d107764, d141564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d107765 q = 1) (hb : d141565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107765, d141565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d107765, d141565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d107766 q = 1) (hb : d141566 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107766, d141566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d107766, d141566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d107767 q = 1) (hb : d141567 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107767, d141567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d107767, d141567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d107768 q = 1) (hb : d141568 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107768, d141568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d107768, d141568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d107769 q = 1) (hb : d141569 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107769, d141569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107769, d141569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro32048 (p : Pattern) (ha : d107776 p = 1) (hb : d141576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107689 q = 1) (hb : d141492 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107689, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32027 q ha hb
    | true =>
      simp only [d107689, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32028 q ha hb
  have h2 (q : Pattern) (ha : d107690 q = 1) (hb : d141493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107690, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107690, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107691 q = 1) (hb : d141494 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107691, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107691, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107692 q = 1) (hb : d141495 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107692, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107692, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107693 q = 1) (hb : d141496 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107693, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107693, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107771 q = 1) (hb : d141571 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107771, d141571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32028 q ha hb
    | true =>
      simp only [d107771, d141571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107772 q = 1) (hb : d141572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107772, d141572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107772, d141572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107773 q = 1) (hb : d141573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107773, d141573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107773, d141573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107774 q = 1) (hb : d141574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107774, d141574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107774, d141574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107775 q = 1) (hb : d141575 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107775, d141575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107775, d141575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107776 q = 1) (hb : d141576 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107776, d141576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107776, d141576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32049 (p : Pattern) (ha : d107782 p = 1) (hb : d141582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107771 q = 1) (hb : d141571 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107771, d141571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32028 q ha hb
    | true =>
      simp only [d107771, d141571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107772 q = 1) (hb : d141572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107772, d141572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107772, d141572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107773 q = 1) (hb : d141573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107773, d141573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107773, d141573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107774 q = 1) (hb : d141574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107774, d141574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107774, d141574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107775 q = 1) (hb : d141575 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107775, d141575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107775, d141575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107777 q = 1) (hb : d141577 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107777, d141577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32031 q ha hb
    | true =>
      simp only [d107777, d141577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107778 q = 1) (hb : d141578 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107778, d141578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107778, d141578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107779 q = 1) (hb : d141579 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107779, d141579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107779, d141579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107780 q = 1) (hb : d141580 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107780, d141580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107780, d141580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107781 q = 1) (hb : d141581 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107781, d141581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107781, d141581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107782 q = 1) (hb : d141582 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107782, d141582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107782, d141582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32050 (p : Pattern) (ha : d107789 p = 1) (hb : d141589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107761 q = 1) (hb : d141561 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107761, d141561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32045 q ha hb
    | true =>
      simp only [d107761, d141561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32030 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107699 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107762 q = 1) (hb : d141562 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107762, d141562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107762, d141562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d107764 q = 1) (hb : d141564 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107764, d141564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32046 q ha hb
    | true =>
      simp only [d107764, d141564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107765 q = 1) (hb : d141565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107765, d141565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107765, d141565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107766 q = 1) (hb : d141566 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107766, d141566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107766, d141566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107787 q = 1) (hb : d141587 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107787, d141587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107787, d141587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107788 q = 1) (hb : d141588 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107788, d141588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107788, d141588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107789 q = 1) (hb : d141589 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107789, d141589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107789, d141589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32051 (p : Pattern) (ha : d107791 p = 1) (hb : d141591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107777 q = 1) (hb : d141577 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107777, d141577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32031 q ha hb
    | true =>
      simp only [d107777, d141577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107778 q = 1) (hb : d141578 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107778, d141578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107778, d141578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107779 q = 1) (hb : d141579 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107779, d141579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107779, d141579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107780 q = 1) (hb : d141580 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107780, d141580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107780, d141580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107781 q = 1) (hb : d141581 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107781, d141581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107781, d141581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107791 q = 1) (hb : d141591 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107791, d141591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107791, d141591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32052 (p : Pattern) (ha : d107802 p = 1) (hb : d141599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107797 q = 1) (hb : d114500 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107797, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28737 q hb ha
    | true =>
      simp only [d107797, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107798 q = 1) (hb : d114501 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107798, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107798, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107799 q = 1) (hb : d114502 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107799, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107799, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107636 q = 1) (hb : d114363 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107636, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22850 q hb ha
    | true =>
      simp only [d107636, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107637 q = 1) (hb : d114364 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107637, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107637, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107638 q = 1) (hb : d114365 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107638, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107638, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107800 q = 1) (hb : d141597 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107800, d141597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107800, d141597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88402 q = 1) (hb : d107523 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88402, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10566 q ha hb
    | true =>
      simp only [d88402, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d88403 q = 1) (hb : d107524 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88403, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88403, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88404 q = 1) (hb : d107525 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88404, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88404, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107639 q = 1) (hb : d141443 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107639, d141443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107639, d141443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d107801 q = 1) (hb : d141598 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107801, d141598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107801, d141598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107802 q = 1) (hb : d141599 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107802, d141599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107802, d141599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro32053 (p : Pattern) (ha : d107807 p = 1) (hb : d141603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107636 q = 1) (hb : d114363 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107636, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22850 q hb ha
    | true =>
      simp only [d107636, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107637 q = 1) (hb : d114364 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107637, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107637, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107638 q = 1) (hb : d114365 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107638, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107638, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88402 q = 1) (hb : d107523 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88402, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10566 q ha hb
    | true =>
      simp only [d88402, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88403 q = 1) (hb : d107524 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88403, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88403, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88404 q = 1) (hb : d107525 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88404, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88404, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107639 q = 1) (hb : d141443 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107639, d141443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107639, d141443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d88405 q = 1) (hb : d107805 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88405, d107805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d88405, d107805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d107806 q = 1) (hb : d141602 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107806, d141602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107806, d141602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107807 q = 1) (hb : d141603 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107807, d141603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107807, d141603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32054 (p : Pattern) (ha : d107813 p = 1) (hb : d141609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107803 q = 1) (hb : d141600 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107803, d141600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32052 q ha hb
    | true =>
      simp only [d107803, d141600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107804 q = 1) (hb : d141601 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107804, d141601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107804, d141601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107808 q = 1) (hb : d141604 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107808, d141604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32053 q ha hb
    | true =>
      simp only [d107808, d141604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107809 q = 1) (hb : d141605 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107809, d141605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107809, d141605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107810 q = 1) (hb : d141606 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107810, d141606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107810, d141606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107811 q = 1) (hb : d141607 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107811, d141607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107811, d141607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107812 q = 1) (hb : d141608 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107812, d141608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107812, d141608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107813 q = 1) (hb : d141609 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107813, d141609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107813, d141609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32055 (p : Pattern) (ha : d107815 p = 1) (hb : d141611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88402 q = 1) (hb : d107523 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88402, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10566 q ha hb
    | true =>
      simp only [d88402, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d88403 q = 1) (hb : d107524 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88403, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88403, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d88404 q = 1) (hb : d107525 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88404, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88404, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88405 q = 1) (hb : d107805 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88405, d107805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88405, d107805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d107814 q = 1) (hb : d141610 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107814, d141610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107814, d141610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107815 q = 1) (hb : d141611 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107815, d141611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107815, d141611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32056 (p : Pattern) (ha : d107821 p = 1) (hb : d141617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107808 q = 1) (hb : d141604 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107808, d141604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32053 q ha hb
    | true =>
      simp only [d107808, d141604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107809 q = 1) (hb : d141605 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107809, d141605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107809, d141605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107816 q = 1) (hb : d141612 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107816, d141612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32055 q ha hb
    | true =>
      simp only [d107816, d141612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107817 q = 1) (hb : d141613 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107817, d141613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107817, d141613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107818 q = 1) (hb : d141614 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107818, d141614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107818, d141614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107819 q = 1) (hb : d141615 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107819, d141615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107819, d141615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107820 q = 1) (hb : d141616 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107820, d141616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107820, d141616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107821 q = 1) (hb : d141617 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107821, d141617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107821, d141617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32057 (p : Pattern) (ha : d107832 p = 1) (hb : d141623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107808 q = 1) (hb : d141604 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107808, d141604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32053 q ha hb
    | true =>
      simp only [d107808, d141604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107809 q = 1) (hb : d141605 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107809, d141605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107809, d141605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107829 q = 1) (hb : d141620 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107829, d141620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107829, d141620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107830 q = 1) (hb : d141621 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107830, d141621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107830, d141621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107831 q = 1) (hb : d141622 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107831, d141622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107831, d141622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107832 q = 1) (hb : d141623 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107832, d141623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107832, d141623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32058 (p : Pattern) (ha : d107838 p = 1) (hb : d141629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107822 q = 1) (hb : d141618 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107822, d141618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32054 q ha hb
    | true =>
      simp only [d107822, d141618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32056 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107827 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107828 q = 1) (hb : d141619 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107828, d141619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107828, d141619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d107833 q = 1) (hb : d141624 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107833, d141624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32057 q ha hb
    | true =>
      simp only [d107833, d141624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107834 q = 1) (hb : d141625 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107834, d141625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107834, d141625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107835 q = 1) (hb : d141626 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107835, d141626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107835, d141626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107836 q = 1) (hb : d141627 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107836, d141627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107836, d141627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107837 q = 1) (hb : d141628 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107837, d141628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107837, d141628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107838 q = 1) (hb : d141629 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107838, d141629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107838, d141629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32059 (p : Pattern) (ha : d107826 p = 1) (hb : d141634 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107816 q = 1) (hb : d141612 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107816, d141612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32055 q ha hb
    | true =>
      simp only [d107816, d141612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107817 q = 1) (hb : d141613 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107817, d141613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107817, d141613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107823 q = 1) (hb : d141631 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107823, d141631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107823, d141631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107824 q = 1) (hb : d141632 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107824, d141632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107824, d141632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107825 q = 1) (hb : d141633 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107825, d141633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107825, d141633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107826 q = 1) (hb : d141634 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107826, d141634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107826, d141634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32060 (p : Pattern) (ha : d107845 p = 1) (hb : d141640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107840 q = 1) (hb : d141635 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107840, d141635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32059 q ha hb
    | true =>
      simp only [d107840, d141635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107841 q = 1) (hb : d141636 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107841, d141636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107841, d141636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107842 q = 1) (hb : d141637 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107842, d141637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107842, d141637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107843 q = 1) (hb : d141638 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107843, d141638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107843, d141638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107844 q = 1) (hb : d141639 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107844, d141639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107844, d141639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107845 q = 1) (hb : d141640 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107845, d141640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107845, d141640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32061 (p : Pattern) (ha : d107851 p = 1) (hb : d141646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107695 q = 1) (hb : d141498 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107695, d141498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107695, d141498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32029 q ha hb
  have h2 (q : Pattern) (ha : d107696 q = 1) (hb : d141499 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107696, d141499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107696, d141499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107705 q = 1) (hb : d141508 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107705, d141508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32029 q ha hb
    | true =>
      simp only [d107705, d141508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32032 q ha hb
  have h4 (q : Pattern) (ha : d107706 q = 1) (hb : d141509 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107706, d141509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107706, d141509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107707 q = 1) (hb : d141510 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107707, d141510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107707, d141510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107770 q = 1) (hb : d141570 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107770, d141570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32040 q ha hb
    | true =>
      simp only [d107770, d141570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32047 q ha hb
  have h7 (q : Pattern) (ha : d107783 q = 1) (hb : d141583 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107783, d141583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32048 q ha hb
    | true =>
      simp only [d107783, d141583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32049 q ha hb
  have h8 (q : Pattern) (ha : d107784 q = 1) (hb : d141584 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107784, d141584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107784, d141584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107785 q = 1) (hb : d141585 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107785, d141585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107785, d141585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d107786 q = 1) (hb : d141586 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107786, d141586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107786, d141586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107790 q = 1) (hb : d141590 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107790, d141590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107790, d141590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32050 q ha hb
  have h12 (q : Pattern) (ha : d107792 q = 1) (hb : d141592 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107792, d141592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107792, d141592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32051 q ha hb
  have h13 (q : Pattern) (ha : d107793 q = 1) (hb : d141593 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107793, d141593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107793, d141593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107794 q = 1) (hb : d141594 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107794, d141594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107794, d141594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d107795 q = 1) (hb : d141595 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107795, d141595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d107795, d141595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d107796 q = 1) (hb : d141596 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107796, d141596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107796, d141596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107839 q = 1) (hb : d141630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107839, d141630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107839, d141630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32058 q ha hb
  have h18 (q : Pattern) (ha : d107846 q = 1) (hb : d141641 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107846, d141641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107846, d141641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32060 q ha hb
  have h19 (q : Pattern) (ha : d107847 q = 1) (hb : d141642 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107847, d141642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107847, d141642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d107848 q = 1) (hb : d141643 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107848, d141643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d107848, d141643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d107849 q = 1) (hb : d141644 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107849, d141644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d107849, d141644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d107850 q = 1) (hb : d141645 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107850, d141645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d107850, d141645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107851 q = 1) (hb : d141646 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107851, d141646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d107851, d141646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro32062 (p : Pattern) (ha : d107857 p = 1) (hb : d141652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107852 q = 1) (hb : d141647 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107852, d141647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107852, d141647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32061 q ha hb
  have h2 (q : Pattern) (ha : d107853 q = 1) (hb : d141648 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107853, d141648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107853, d141648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107854 q = 1) (hb : d141649 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107854, d141649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107854, d141649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107855 q = 1) (hb : d141650 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107855, d141650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107855, d141650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107856 q = 1) (hb : d141651 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107856, d141651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107856, d141651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107857 q = 1) (hb : d141652 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d107857, d141652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107857, d141652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32063 (p : Pattern) (ha : d107868 p = 1) (hb : d141656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107859 q = 1) (hb : d114443 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107859, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22866 q hb ha
    | true =>
      simp only [d107859, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107860 q = 1) (hb : d114444 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107860, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107860, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107861 q = 1) (hb : d114445 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107861, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107861, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88489 q = 1) (hb : d107862 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88489, d107862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10581 q ha hb
    | true =>
      simp only [d88489, d107862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88490 q = 1) (hb : d107863 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88490, d107863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88490, d107863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88491 q = 1) (hb : d107864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88491, d107864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88491, d107864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107865 q = 1) (hb : d141654 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107865, d141654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107865, d141654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d88492 q = 1) (hb : d107866 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88492, d107866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d88492, d107866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d107867 q = 1) (hb : d141655 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107867, d141655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107867, d141655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d107868 q = 1) (hb : d141656 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107868, d141656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107868, d141656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32064 (p : Pattern) (ha : d107872 p = 1) (hb : d141660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88489 q = 1) (hb : d107862 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88489, d107862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10581 q ha hb
    | true =>
      simp only [d88489, d107862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d88490 q = 1) (hb : d107863 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88490, d107863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88490, d107863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d88491 q = 1) (hb : d107864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88491, d107864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88491, d107864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88492 q = 1) (hb : d107866 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88492, d107866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88492, d107866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d107871 q = 1) (hb : d141659 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107871, d141659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107871, d141659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107872 q = 1) (hb : d141660 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107872, d141660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107872, d141660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32065 (p : Pattern) (ha : d107878 p = 1) (hb : d141666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107869 q = 1) (hb : d141657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32063 q ha hb
    | true =>
      simp only [d107869, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107870 q = 1) (hb : d141658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107873 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32064 q ha hb
    | true =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107874 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107875 q = 1) (hb : d141663 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107875, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107875, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107876 q = 1) (hb : d141664 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107876, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107876, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107877 q = 1) (hb : d141665 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107877, d141665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107877, d141665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107878 q = 1) (hb : d141666 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107878, d141666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107878, d141666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32066 (p : Pattern) (ha : d107882 p = 1) (hb : d141670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107873 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32064 q ha hb
    | true =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107874 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107879 q = 1) (hb : d141667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107879, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107879, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107880 q = 1) (hb : d141668 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107880, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107880, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107881 q = 1) (hb : d141669 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107881, d141669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107881, d141669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107882 q = 1) (hb : d141670 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107882, d141670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107882, d141670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32067 (p : Pattern) (ha : d107888 p = 1) (hb : d141676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107883 q = 1) (hb : d141671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107883, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32065 q ha hb
    | true =>
      simp only [d107883, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32066 q ha hb
  have h2 (q : Pattern) (ha : d107884 q = 1) (hb : d141672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107884, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107884, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107885 q = 1) (hb : d141673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107885, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107885, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107886 q = 1) (hb : d141674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107886, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107886, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107887 q = 1) (hb : d141675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107887, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107887, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107888 q = 1) (hb : d141676 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107888, d141676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107888, d141676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32068 (p : Pattern) (ha : d107891 p = 1) (hb : d141679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107869 q = 1) (hb : d141657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32063 q ha hb
    | true =>
      simp only [d107869, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107870 q = 1) (hb : d141658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107873 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32064 q ha hb
    | true =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107874 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107875 q = 1) (hb : d141663 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107875, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107875, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107876 q = 1) (hb : d141664 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107876, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107876, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107877 q = 1) (hb : d141665 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107877, d141665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107877, d141665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107891 q = 1) (hb : d141679 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107891, d141679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107891, d141679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32069 (p : Pattern) (ha : d107892 p = 1) (hb : d141680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107873 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32064 q ha hb
    | true =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107874 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107879 q = 1) (hb : d141667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107879, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107879, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107880 q = 1) (hb : d141668 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107880, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107880, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107881 q = 1) (hb : d141669 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107881, d141669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107881, d141669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107892 q = 1) (hb : d141680 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107892, d141680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107892, d141680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32070 (p : Pattern) (ha : d107898 p = 1) (hb : d141686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107883 q = 1) (hb : d141671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107883, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32065 q ha hb
    | true =>
      simp only [d107883, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32066 q ha hb
  have h2 (q : Pattern) (ha : d107884 q = 1) (hb : d141672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107884, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107884, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107885 q = 1) (hb : d141673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107885, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107885, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107886 q = 1) (hb : d141674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107886, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107886, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107887 q = 1) (hb : d141675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107887, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107887, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107893 q = 1) (hb : d141681 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107893, d141681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32068 q ha hb
    | true =>
      simp only [d107893, d141681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32069 q ha hb
  have h7 (q : Pattern) (ha : d107894 q = 1) (hb : d141682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107894, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107894, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107895 q = 1) (hb : d141683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107895, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107895, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107896 q = 1) (hb : d141684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107896, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107896, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107897 q = 1) (hb : d141685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107897, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107897, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107898 q = 1) (hb : d141686 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107898, d141686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107898, d141686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32071 (p : Pattern) (ha : d107903 p = 1) (hb : d141691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107869 q = 1) (hb : d141657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32063 q ha hb
    | true =>
      simp only [d107869, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107870 q = 1) (hb : d141658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107873 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32064 q ha hb
    | true =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107874 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107875 q = 1) (hb : d141663 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107875, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107875, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107876 q = 1) (hb : d141664 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107876, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107876, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107902 q = 1) (hb : d141690 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107902, d141690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107902, d141690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107903 q = 1) (hb : d141691 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107903, d141691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107903, d141691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32072 (p : Pattern) (ha : d107905 p = 1) (hb : d141693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107873 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32064 q ha hb
    | true =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107874 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107879 q = 1) (hb : d141667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107879, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107879, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107880 q = 1) (hb : d141668 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107880, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107880, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107904 q = 1) (hb : d141692 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107904, d141692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107904, d141692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107905 q = 1) (hb : d141693 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107905, d141693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107905, d141693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32073 (p : Pattern) (ha : d107912 p = 1) (hb : d141700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107869 q = 1) (hb : d141657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32063 q ha hb
    | true =>
      simp only [d107869, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107870 q = 1) (hb : d141658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107873 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32064 q ha hb
    | true =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107874 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107875 q = 1) (hb : d141663 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107875, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107875, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107910 q = 1) (hb : d141698 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107910, d141698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107910, d141698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107911 q = 1) (hb : d141699 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107911, d141699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107911, d141699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107912 q = 1) (hb : d141700 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107912, d141700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107912, d141700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32074 (p : Pattern) (ha : d107915 p = 1) (hb : d141703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107873 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32064 q ha hb
    | true =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107874 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107879 q = 1) (hb : d141667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107879, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107879, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107913 q = 1) (hb : d141701 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107913, d141701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107913, d141701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107914 q = 1) (hb : d141702 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107914, d141702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107914, d141702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107915 q = 1) (hb : d141703 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107915, d141703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107915, d141703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32075 (p : Pattern) (ha : d107924 p = 1) (hb : d141712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107919 q = 1) (hb : d141707 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107919, d141707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28763 q hb ha
    | true =>
      simp only [d107919, d141707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107920 q = 1) (hb : d141708 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107920, d141708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107920, d141708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107921 q = 1) (hb : d141709 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107921, d141709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107921, d141709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107859 q = 1) (hb : d114443 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107859, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22866 q hb ha
    | true =>
      simp only [d107859, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107860 q = 1) (hb : d114444 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107860, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107860, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107861 q = 1) (hb : d114445 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107861, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107861, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107922 q = 1) (hb : d141710 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107922, d141710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107922, d141710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88489 q = 1) (hb : d107862 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88489, d107862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10581 q ha hb
    | true =>
      simp only [d88489, d107862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d88490 q = 1) (hb : d107863 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88490, d107863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88490, d107863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88491 q = 1) (hb : d107864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88491, d107864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88491, d107864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107865 q = 1) (hb : d141654 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107865, d141654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107865, d141654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d107923 q = 1) (hb : d141711 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107923, d141711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107923, d141711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107924 q = 1) (hb : d141712 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107924, d141712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107924, d141712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro32076 (p : Pattern) (ha : d107930 p = 1) (hb : d141718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107925 q = 1) (hb : d141713 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107925, d141713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32075 q ha hb
    | true =>
      simp only [d107925, d141713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107926 q = 1) (hb : d141714 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107926, d141714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107926, d141714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107869 q = 1) (hb : d141657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32063 q ha hb
    | true =>
      simp only [d107869, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107870 q = 1) (hb : d141658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107927 q = 1) (hb : d141715 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107927, d141715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107927, d141715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107928 q = 1) (hb : d141716 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107928, d141716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107928, d141716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107929 q = 1) (hb : d141717 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107929, d141717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107929, d141717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107930 q = 1) (hb : d141718 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107930, d141718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107930, d141718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32077 (p : Pattern) (ha : d107938 p = 1) (hb : d141656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107859 q = 1) (hb : d114443 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107859, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22866 q hb ha
    | true =>
      simp only [d107859, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107860 q = 1) (hb : d114444 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d107860, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107860, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107861 q = 1) (hb : d114445 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d107861, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107861, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88489 q = 1) (hb : d107862 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88489, d107862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10581 q ha hb
    | true =>
      simp only [d88489, d107862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88490 q = 1) (hb : d107863 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88490, d107863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88490, d107863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88491 q = 1) (hb : d107864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88491, d107864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88491, d107864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107865 q = 1) (hb : d141654 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d107865, d141654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107865, d141654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d88489 q = 1) (hb : d107933 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88489, d107933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22869 q ha hb
    | true =>
      simp only [d88489, d107933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d88490 q = 1) (hb : d107934 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88490, d107934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88490, d107934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88491 q = 1) (hb : d107935 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88491, d107935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88491, d107935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d88492 q = 1) (hb : d107936 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88492, d107936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88492, d107936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d107937 q = 1) (hb : d141655 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d107937, d141655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107937, d141655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d107938 q = 1) (hb : d141656 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d107938, d141656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107938, d141656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro32078 (p : Pattern) (ha : d107944 p = 1) (hb : d141724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107939 q = 1) (hb : d141657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107939, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32077 q ha hb
    | true =>
      simp only [d107939, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107940 q = 1) (hb : d141658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107940, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107940, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107941 q = 1) (hb : d141721 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107941, d141721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107941, d141721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107942 q = 1) (hb : d141722 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107942, d141722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107942, d141722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107943 q = 1) (hb : d141723 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107943, d141723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107943, d141723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107944 q = 1) (hb : d141724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107944, d141724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107944, d141724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32079 (p : Pattern) (ha : d107950 p = 1) (hb : d141730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107906 q = 1) (hb : d141694 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107906, d141694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32071 q ha hb
    | true =>
      simp only [d107906, d141694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32072 q ha hb
  have h2 (q : Pattern) (ha : d107907 q = 1) (hb : d141695 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107907, d141695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107907, d141695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107908 q = 1) (hb : d141696 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107908, d141696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107908, d141696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107909 q = 1) (hb : d141697 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107909, d141697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107909, d141697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107916 q = 1) (hb : d141704 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107916, d141704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32073 q ha hb
    | true =>
      simp only [d107916, d141704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32074 q ha hb
  have h6 (q : Pattern) (ha : d107917 q = 1) (hb : d141705 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107917, d141705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107917, d141705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107918 q = 1) (hb : d141706 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107918, d141706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107918, d141706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107931 q = 1) (hb : d141719 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107931, d141719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32076 q ha hb
    | true =>
      simp only [d107931, d141719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32065 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107883 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107932 q = 1) (hb : d141720 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107932, d141720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107932, d141720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d107945 q = 1) (hb : d141725 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107945, d141725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32078 q ha hb
    | true =>
      simp only [d107945, d141725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107946 q = 1) (hb : d141726 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107946, d141726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107946, d141726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107947 q = 1) (hb : d141727 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107947, d141727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107947, d141727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107948 q = 1) (hb : d141728 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107948, d141728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107948, d141728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107949 q = 1) (hb : d141729 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107949, d141729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107949, d141729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107950 q = 1) (hb : d141730 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107950, d141730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107950, d141730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro32080 (p : Pattern) (ha : d107951 p = 1) (hb : d141731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107869 q = 1) (hb : d141657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32063 q ha hb
    | true =>
      simp only [d107869, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107870 q = 1) (hb : d141658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107873 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32064 q ha hb
    | true =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107874 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107875 q = 1) (hb : d141663 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107875, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107875, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107876 q = 1) (hb : d141664 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107876, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107876, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107902 q = 1) (hb : d141690 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107902, d141690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107902, d141690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107951 q = 1) (hb : d141731 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107951, d141731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107951, d141731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32081 (p : Pattern) (ha : d107952 p = 1) (hb : d141732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107873 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32064 q ha hb
    | true =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107874 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107879 q = 1) (hb : d141667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107879, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107879, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107880 q = 1) (hb : d141668 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107880, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107880, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107904 q = 1) (hb : d141692 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107904, d141692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107904, d141692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107952 q = 1) (hb : d141732 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107952, d141732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107952, d141732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32082 (p : Pattern) (ha : d107957 p = 1) (hb : d141737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107869 q = 1) (hb : d141657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32063 q ha hb
    | true =>
      simp only [d107869, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107870 q = 1) (hb : d141658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107873 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32064 q ha hb
    | true =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107874 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107875 q = 1) (hb : d141663 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107875, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107875, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107910 q = 1) (hb : d141698 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107910, d141698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107910, d141698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107911 q = 1) (hb : d141699 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107911, d141699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107911, d141699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107957 q = 1) (hb : d141737 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107957, d141737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107957, d141737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32083 (p : Pattern) (ha : d107958 p = 1) (hb : d141738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107873 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32064 q ha hb
    | true =>
      simp only [d107873, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107874 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107874, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107879 q = 1) (hb : d141667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107879, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107879, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107913 q = 1) (hb : d141701 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107913, d141701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107913, d141701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107914 q = 1) (hb : d141702 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107914, d141702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107914, d141702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107958 q = 1) (hb : d141738 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107958, d141738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107958, d141738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32084 (p : Pattern) (ha : d107962 p = 1) (hb : d141742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107925 q = 1) (hb : d141713 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107925, d141713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32075 q ha hb
    | true =>
      simp only [d107925, d141713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107926 q = 1) (hb : d141714 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107926, d141714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107926, d141714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107869 q = 1) (hb : d141657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107869, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32063 q ha hb
    | true =>
      simp only [d107869, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107870 q = 1) (hb : d141658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107870, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107870, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107927 q = 1) (hb : d141715 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107927, d141715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107927, d141715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107928 q = 1) (hb : d141716 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107928, d141716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107928, d141716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107929 q = 1) (hb : d141717 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107929, d141717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107929, d141717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107962 q = 1) (hb : d141742 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107962, d141742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107962, d141742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32085 (p : Pattern) (ha : d107965 p = 1) (hb : d141745 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107939 q = 1) (hb : d141657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d107939, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32077 q ha hb
    | true =>
      simp only [d107939, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107940 q = 1) (hb : d141658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d107940, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107940, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107941 q = 1) (hb : d141721 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d107941, d141721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107941, d141721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107942 q = 1) (hb : d141722 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d107942, d141722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107942, d141722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107943 q = 1) (hb : d141723 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d107943, d141723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107943, d141723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107965 q = 1) (hb : d141745 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d107965, d141745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107965, d141745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32086 (p : Pattern) (ha : d107971 p = 1) (hb : d141751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107906 q = 1) (hb : d141694 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107906, d141694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32071 q ha hb
    | true =>
      simp only [d107906, d141694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32072 q ha hb
  have h2 (q : Pattern) (ha : d107907 q = 1) (hb : d141695 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107907, d141695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107907, d141695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107908 q = 1) (hb : d141696 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107908, d141696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107908, d141696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107909 q = 1) (hb : d141697 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107909, d141697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107909, d141697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107916 q = 1) (hb : d141704 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107916, d141704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32073 q ha hb
    | true =>
      simp only [d107916, d141704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32074 q ha hb
  have h6 (q : Pattern) (ha : d107917 q = 1) (hb : d141705 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107917, d141705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107917, d141705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107918 q = 1) (hb : d141706 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107918, d141706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107918, d141706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107931 q = 1) (hb : d141719 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107931, d141719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32076 q ha hb
    | true =>
      simp only [d107931, d141719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32065 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107883 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107932 q = 1) (hb : d141720 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107932, d141720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107932, d141720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d107945 q = 1) (hb : d141725 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107945, d141725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32078 q ha hb
    | true =>
      simp only [d107945, d141725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107946 q = 1) (hb : d141726 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107946, d141726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107946, d141726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107947 q = 1) (hb : d141727 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107947, d141727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107947, d141727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107948 q = 1) (hb : d141728 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107948, d141728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107948, d141728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107949 q = 1) (hb : d141729 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107949, d141729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107949, d141729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107953 q = 1) (hb : d141733 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107953, d141733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32080 q ha hb
    | true =>
      simp only [d107953, d141733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32081 q ha hb
  have h17 (q : Pattern) (ha : d107954 q = 1) (hb : d141734 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107954, d141734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107954, d141734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d107955 q = 1) (hb : d141735 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107955, d141735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107955, d141735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d107956 q = 1) (hb : d141736 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107956, d141736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107956, d141736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d107959 q = 1) (hb : d141739 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107959, d141739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32082 q ha hb
    | true =>
      simp only [d107959, d141739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32083 q ha hb
  have h21 (q : Pattern) (ha : d107960 q = 1) (hb : d141740 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107960, d141740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107960, d141740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d107961 q = 1) (hb : d141741 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107961, d141741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d107961, d141741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107963 q = 1) (hb : d141743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107963, d141743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32084 q ha hb
    | true =>
      simp only [d107963, d141743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32068 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d107893 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d107964 q = 1) (hb : d141744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107964, d141744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d107964, d141744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d107966 q = 1) (hb : d141746 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107966, d141746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32085 q ha hb
    | true =>
      simp only [d107966, d141746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d107967 q = 1) (hb : d141747 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107967, d141747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d107967, d141747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d107968 q = 1) (hb : d141748 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107968, d141748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d107968, d141748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d107969 q = 1) (hb : d141749 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107969, d141749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d107969, d141749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d107970 q = 1) (hb : d141750 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107970, d141750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d107970, d141750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d107971 q = 1) (hb : d141751 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107971, d141751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107971, d141751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro32087 (p : Pattern) (ha : d107978 p = 1) (hb : d141758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107883 q = 1) (hb : d141671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107883, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32065 q ha hb
    | true =>
      simp only [d107883, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32066 q ha hb
  have h2 (q : Pattern) (ha : d107884 q = 1) (hb : d141672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107884, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107884, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107885 q = 1) (hb : d141673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107885, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107885, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107886 q = 1) (hb : d141674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107886, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107886, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107887 q = 1) (hb : d141675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107887, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107887, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107973 q = 1) (hb : d141753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107973, d141753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32066 q ha hb
    | true =>
      simp only [d107973, d141753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107974 q = 1) (hb : d141754 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107974, d141754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107974, d141754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107975 q = 1) (hb : d141755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107975, d141755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107975, d141755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107976 q = 1) (hb : d141756 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107976, d141756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107976, d141756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107977 q = 1) (hb : d141757 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107977, d141757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107977, d141757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107978 q = 1) (hb : d141758 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107978, d141758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107978, d141758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32088 (p : Pattern) (ha : d107984 p = 1) (hb : d141764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107973 q = 1) (hb : d141753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107973, d141753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32066 q ha hb
    | true =>
      simp only [d107973, d141753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107974 q = 1) (hb : d141754 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107974, d141754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107974, d141754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107975 q = 1) (hb : d141755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107975, d141755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107975, d141755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107976 q = 1) (hb : d141756 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107976, d141756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107976, d141756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107977 q = 1) (hb : d141757 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107977, d141757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107977, d141757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107979 q = 1) (hb : d141759 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107979, d141759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32069 q ha hb
    | true =>
      simp only [d107979, d141759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107980 q = 1) (hb : d141760 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107980, d141760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107980, d141760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107981 q = 1) (hb : d141761 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107981, d141761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d107981, d141761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107982 q = 1) (hb : d141762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107982, d141762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107982, d141762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107983 q = 1) (hb : d141763 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107983, d141763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107983, d141763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107984 q = 1) (hb : d141764 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107984, d141764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107984, d141764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32089 (p : Pattern) (ha : d107991 p = 1) (hb : d141771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107963 q = 1) (hb : d141743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107963, d141743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32084 q ha hb
    | true =>
      simp only [d107963, d141743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32068 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107893 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107964 q = 1) (hb : d141744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107964, d141744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107964, d141744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d107966 q = 1) (hb : d141746 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107966, d141746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32085 q ha hb
    | true =>
      simp only [d107966, d141746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107967 q = 1) (hb : d141747 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107967, d141747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d107967, d141747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107968 q = 1) (hb : d141748 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107968, d141748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107968, d141748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107989 q = 1) (hb : d141769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107989, d141769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107989, d141769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107990 q = 1) (hb : d141770 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107990, d141770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107990, d141770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107991 q = 1) (hb : d141771 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107991, d141771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107991, d141771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32090 (p : Pattern) (ha : d107993 p = 1) (hb : d141773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107979 q = 1) (hb : d141759 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d107979, d141759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32069 q ha hb
    | true =>
      simp only [d107979, d141759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107980 q = 1) (hb : d141760 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107980, d141760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107980, d141760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107981 q = 1) (hb : d141761 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107981, d141761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107981, d141761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107982 q = 1) (hb : d141762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107982, d141762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107982, d141762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107983 q = 1) (hb : d141763 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107983, d141763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107983, d141763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107993 q = 1) (hb : d141773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107993, d141773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107993, d141773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32091 (p : Pattern) (ha : d108011 p = 1) (hb : d141785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107999 q = 1) (hb : d141779 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d107999, d141779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28780 q hb ha
    | true =>
      simp only [d107999, d141779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108000 q = 1) (hb : d141780 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108000, d141780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108000, d141780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108001 q = 1) (hb : d141781 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108001, d141781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108001, d141781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108002 q = 1) (hb : d114500 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108002, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22880 q hb ha
    | true =>
      simp only [d108002, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108003 q = 1) (hb : d114501 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108003, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108003, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108004 q = 1) (hb : d114502 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108004, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108004, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108005 q = 1) (hb : d141782 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108005, d141782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108005, d141782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88553 q = 1) (hb : d108006 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88553, d108006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10600 q ha hb
    | true =>
      simp only [d88553, d108006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d88554 q = 1) (hb : d108007 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88554, d108007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88554, d108007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88555 q = 1) (hb : d108008 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88555, d108008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88555, d108008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108009 q = 1) (hb : d141783 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108009, d141783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108009, d141783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d108010 q = 1) (hb : d141784 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108010, d141784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108010, d141784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108011 q = 1) (hb : d141785 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108011, d141785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108011, d141785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro32092 (p : Pattern) (ha : d108016 p = 1) (hb : d141789 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108002 q = 1) (hb : d114500 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108002, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22880 q hb ha
    | true =>
      simp only [d108002, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108003 q = 1) (hb : d114501 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108003, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108003, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108004 q = 1) (hb : d114502 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108004, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108004, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88553 q = 1) (hb : d108006 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88553, d108006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10600 q ha hb
    | true =>
      simp only [d88553, d108006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88554 q = 1) (hb : d108007 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88554, d108007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88554, d108007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88555 q = 1) (hb : d108008 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88555, d108008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88555, d108008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108009 q = 1) (hb : d141783 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108009, d141783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108009, d141783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d88556 q = 1) (hb : d108014 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88556, d108014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d88556, d108014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d108015 q = 1) (hb : d141788 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108015, d141788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108015, d141788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108016 q = 1) (hb : d141789 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108016, d141789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108016, d141789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32093 (p : Pattern) (ha : d108022 p = 1) (hb : d141795 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108012 q = 1) (hb : d141786 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108012, d141786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32091 q ha hb
    | true =>
      simp only [d108012, d141786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108013 q = 1) (hb : d141787 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108013, d141787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108013, d141787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108017 q = 1) (hb : d141790 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108017, d141790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32092 q ha hb
    | true =>
      simp only [d108017, d141790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108018 q = 1) (hb : d141791 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108018, d141791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108018, d141791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108019 q = 1) (hb : d141792 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108019, d141792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108019, d141792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108020 q = 1) (hb : d141793 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108020, d141793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108020, d141793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108021 q = 1) (hb : d141794 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108021, d141794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108021, d141794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108022 q = 1) (hb : d141795 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108022, d141795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108022, d141795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32094 (p : Pattern) (ha : d108024 p = 1) (hb : d141797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88553 q = 1) (hb : d108006 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88553, d108006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10600 q ha hb
    | true =>
      simp only [d88553, d108006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d88554 q = 1) (hb : d108007 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88554, d108007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88554, d108007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d88555 q = 1) (hb : d108008 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88555, d108008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88555, d108008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88556 q = 1) (hb : d108014 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88556, d108014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88556, d108014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108023 q = 1) (hb : d141796 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108023, d141796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108023, d141796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108024 q = 1) (hb : d141797 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108024, d141797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108024, d141797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32095 (p : Pattern) (ha : d108030 p = 1) (hb : d141803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108017 q = 1) (hb : d141790 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108017, d141790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32092 q ha hb
    | true =>
      simp only [d108017, d141790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108018 q = 1) (hb : d141791 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108018, d141791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108018, d141791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108025 q = 1) (hb : d141798 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108025, d141798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32094 q ha hb
    | true =>
      simp only [d108025, d141798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108026 q = 1) (hb : d141799 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108026, d141799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108026, d141799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108027 q = 1) (hb : d141800 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108027, d141800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108027, d141800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108028 q = 1) (hb : d141801 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108028, d141801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108028, d141801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108029 q = 1) (hb : d141802 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108029, d141802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108029, d141802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108030 q = 1) (hb : d141803 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108030, d141803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108030, d141803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32096 (p : Pattern) (ha : d108043 p = 1) (hb : d141789 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108002 q = 1) (hb : d114500 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108002, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22880 q hb ha
    | true =>
      simp only [d108002, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108003 q = 1) (hb : d114501 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108003, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108003, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108004 q = 1) (hb : d114502 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108004, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108004, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88553 q = 1) (hb : d108006 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88553, d108006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10600 q ha hb
    | true =>
      simp only [d88553, d108006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88554 q = 1) (hb : d108007 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88554, d108007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88554, d108007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88555 q = 1) (hb : d108008 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88555, d108008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88555, d108008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108009 q = 1) (hb : d141783 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108009, d141783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108009, d141783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d88553 q = 1) (hb : d108038 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88553, d108038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22885 q ha hb
    | true =>
      simp only [d88553, d108038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d88554 q = 1) (hb : d108039 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88554, d108039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88554, d108039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88555 q = 1) (hb : d108040 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88555, d108040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88555, d108040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d88556 q = 1) (hb : d108041 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88556, d108041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88556, d108041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108042 q = 1) (hb : d141788 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108042, d141788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108042, d141788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d108043 q = 1) (hb : d141789 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108043, d141789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108043, d141789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro32097 (p : Pattern) (ha : d108049 p = 1) (hb : d141809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108044 q = 1) (hb : d141790 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108044, d141790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32096 q ha hb
    | true =>
      simp only [d108044, d141790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108045 q = 1) (hb : d141791 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108045, d141791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108045, d141791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108046 q = 1) (hb : d141806 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108046, d141806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108046, d141806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108047 q = 1) (hb : d141807 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108047, d141807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108047, d141807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108048 q = 1) (hb : d141808 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108048, d141808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108048, d141808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108049 q = 1) (hb : d141809 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108049, d141809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108049, d141809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32098 (p : Pattern) (ha : d108055 p = 1) (hb : d141815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108031 q = 1) (hb : d141804 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108031, d141804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32093 q ha hb
    | true =>
      simp only [d108031, d141804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32095 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108036 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108037 q = 1) (hb : d141805 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108037, d141805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108037, d141805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108050 q = 1) (hb : d141810 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108050, d141810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32097 q ha hb
    | true =>
      simp only [d108050, d141810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108051 q = 1) (hb : d141811 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108051, d141811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108051, d141811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108052 q = 1) (hb : d141812 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108052, d141812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108052, d141812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108053 q = 1) (hb : d141813 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108053, d141813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108053, d141813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108054 q = 1) (hb : d141814 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108054, d141814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108054, d141814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108055 q = 1) (hb : d141815 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108055, d141815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108055, d141815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32099 (p : Pattern) (ha : d108035 p = 1) (hb : d141820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108025 q = 1) (hb : d141798 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108025, d141798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32094 q ha hb
    | true =>
      simp only [d108025, d141798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108026 q = 1) (hb : d141799 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108026, d141799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108026, d141799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108032 q = 1) (hb : d141817 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108032, d141817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108032, d141817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108033 q = 1) (hb : d141818 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108033, d141818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108033, d141818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108034 q = 1) (hb : d141819 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108034, d141819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108034, d141819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108035 q = 1) (hb : d141820 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108035, d141820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108035, d141820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32100 (p : Pattern) (ha : d108062 p = 1) (hb : d141826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108057 q = 1) (hb : d141821 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108057, d141821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32099 q ha hb
    | true =>
      simp only [d108057, d141821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108058 q = 1) (hb : d141822 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108058, d141822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108058, d141822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108059 q = 1) (hb : d141823 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108059, d141823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108059, d141823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108060 q = 1) (hb : d141824 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108060, d141824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108060, d141824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108061 q = 1) (hb : d141825 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108061, d141825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108061, d141825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108062 q = 1) (hb : d141826 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108062, d141826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108062, d141826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32101 (p : Pattern) (ha : d108068 p = 1) (hb : d141832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107889 q = 1) (hb : d141677 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107889, d141677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107889, d141677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32067 q ha hb
  have h2 (q : Pattern) (ha : d107890 q = 1) (hb : d141678 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107890, d141678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107890, d141678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107899 q = 1) (hb : d141687 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107899, d141687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32067 q ha hb
    | true =>
      simp only [d107899, d141687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32070 q ha hb
  have h4 (q : Pattern) (ha : d107900 q = 1) (hb : d141688 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107900, d141688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107900, d141688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107901 q = 1) (hb : d141689 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107901, d141689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d107901, d141689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107972 q = 1) (hb : d141752 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107972, d141752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32079 q ha hb
    | true =>
      simp only [d107972, d141752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32086 q ha hb
  have h7 (q : Pattern) (ha : d107985 q = 1) (hb : d141765 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107985, d141765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32087 q ha hb
    | true =>
      simp only [d107985, d141765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32088 q ha hb
  have h8 (q : Pattern) (ha : d107986 q = 1) (hb : d141766 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107986, d141766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107986, d141766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107987 q = 1) (hb : d141767 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107987, d141767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107987, d141767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d107988 q = 1) (hb : d141768 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107988, d141768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d107988, d141768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107992 q = 1) (hb : d141772 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107992, d141772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107992, d141772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32089 q ha hb
  have h12 (q : Pattern) (ha : d107994 q = 1) (hb : d141774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107994, d141774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107994, d141774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32090 q ha hb
  have h13 (q : Pattern) (ha : d107995 q = 1) (hb : d141775 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107995, d141775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107995, d141775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107996 q = 1) (hb : d141776 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107996, d141776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107996, d141776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d107997 q = 1) (hb : d141777 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107997, d141777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d107997, d141777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d107998 q = 1) (hb : d141778 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107998, d141778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107998, d141778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108056 q = 1) (hb : d141816 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108056, d141816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108056, d141816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32098 q ha hb
  have h18 (q : Pattern) (ha : d108063 q = 1) (hb : d141827 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108063, d141827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108063, d141827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32100 q ha hb
  have h19 (q : Pattern) (ha : d108064 q = 1) (hb : d141828 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108064, d141828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108064, d141828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108065 q = 1) (hb : d141829 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108065, d141829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108065, d141829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d108066 q = 1) (hb : d141830 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108066, d141830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108066, d141830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d108067 q = 1) (hb : d141831 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108067, d141831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108067, d141831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d108068 q = 1) (hb : d141832 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108068, d141832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108068, d141832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro32102 (p : Pattern) (ha : d108074 p = 1) (hb : d141838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108069 q = 1) (hb : d141833 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108069, d141833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108069, d141833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32101 q ha hb
  have h2 (q : Pattern) (ha : d108070 q = 1) (hb : d141834 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108070, d141834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108070, d141834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108071 q = 1) (hb : d141835 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108071, d141835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108071, d141835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108072 q = 1) (hb : d141836 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108072, d141836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108072, d141836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108073 q = 1) (hb : d141837 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108073, d141837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108073, d141837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108074 q = 1) (hb : d141838 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108074, d141838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108074, d141838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32103 (p : Pattern) (ha : d108086 p = 1) (hb : d141843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108077 q = 1) (hb : d114586 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108077, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22898 q hb ha
    | true =>
      simp only [d108077, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108078 q = 1) (hb : d114587 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108078, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108078, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108079 q = 1) (hb : d114588 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108079, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108079, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88641 q = 1) (hb : d108080 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88641, d108080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10613 q ha hb
    | true =>
      simp only [d88641, d108080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88642 q = 1) (hb : d108081 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88642, d108081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88642, d108081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88643 q = 1) (hb : d108082 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88643, d108082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88643, d108082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108083 q = 1) (hb : d141841 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108083, d141841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108083, d141841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d88644 q = 1) (hb : d108084 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88644, d108084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d88644, d108084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d108085 q = 1) (hb : d141842 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108085, d141842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108085, d141842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108086 q = 1) (hb : d141843 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108086, d141843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108086, d141843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32104 (p : Pattern) (ha : d108090 p = 1) (hb : d141847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88641 q = 1) (hb : d108080 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88641, d108080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10613 q ha hb
    | true =>
      simp only [d88641, d108080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d88642 q = 1) (hb : d108081 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88642, d108081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88642, d108081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d88643 q = 1) (hb : d108082 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88643, d108082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88643, d108082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88644 q = 1) (hb : d108084 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88644, d108084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88644, d108084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108089 q = 1) (hb : d141846 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108089, d141846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108089, d141846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108090 q = 1) (hb : d141847 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108090, d141847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108090, d141847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32105 (p : Pattern) (ha : d108096 p = 1) (hb : d141853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108087 q = 1) (hb : d141844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32103 q ha hb
    | true =>
      simp only [d108087, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108088 q = 1) (hb : d141845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108091 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32104 q ha hb
    | true =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108092 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108093 q = 1) (hb : d141850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108093, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108093, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108094 q = 1) (hb : d141851 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108094, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108094, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108095 q = 1) (hb : d141852 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108095, d141852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108095, d141852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108096 q = 1) (hb : d141853 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108096, d141853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108096, d141853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32106 (p : Pattern) (ha : d108100 p = 1) (hb : d141857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108091 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32104 q ha hb
    | true =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108092 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108097 q = 1) (hb : d141854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108097, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108097, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108098 q = 1) (hb : d141855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108098, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108098, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108099 q = 1) (hb : d141856 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108099, d141856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108099, d141856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108100 q = 1) (hb : d141857 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108100, d141857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108100, d141857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32107 (p : Pattern) (ha : d108106 p = 1) (hb : d141863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108101 q = 1) (hb : d141858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108101, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32105 q ha hb
    | true =>
      simp only [d108101, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32106 q ha hb
  have h2 (q : Pattern) (ha : d108102 q = 1) (hb : d141859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108102, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108102, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108103 q = 1) (hb : d141860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108103, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108103, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108104 q = 1) (hb : d141861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108104, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108104, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108105 q = 1) (hb : d141862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108105, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108105, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108106 q = 1) (hb : d141863 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108106, d141863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108106, d141863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32108 (p : Pattern) (ha : d108109 p = 1) (hb : d141866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108087 q = 1) (hb : d141844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32103 q ha hb
    | true =>
      simp only [d108087, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108088 q = 1) (hb : d141845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108091 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32104 q ha hb
    | true =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108092 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108093 q = 1) (hb : d141850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108093, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108093, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108094 q = 1) (hb : d141851 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108094, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108094, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108095 q = 1) (hb : d141852 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108095, d141852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108095, d141852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108109 q = 1) (hb : d141866 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108109, d141866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108109, d141866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32109 (p : Pattern) (ha : d108110 p = 1) (hb : d141867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108091 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32104 q ha hb
    | true =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108092 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108097 q = 1) (hb : d141854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108097, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108097, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108098 q = 1) (hb : d141855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108098, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108098, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108099 q = 1) (hb : d141856 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108099, d141856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108099, d141856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108110 q = 1) (hb : d141867 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108110, d141867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108110, d141867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32110 (p : Pattern) (ha : d108116 p = 1) (hb : d141873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108101 q = 1) (hb : d141858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108101, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32105 q ha hb
    | true =>
      simp only [d108101, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32106 q ha hb
  have h2 (q : Pattern) (ha : d108102 q = 1) (hb : d141859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108102, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108102, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108103 q = 1) (hb : d141860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108103, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108103, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108104 q = 1) (hb : d141861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108104, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108104, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108105 q = 1) (hb : d141862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108105, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108105, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108111 q = 1) (hb : d141868 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108111, d141868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32108 q ha hb
    | true =>
      simp only [d108111, d141868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32109 q ha hb
  have h7 (q : Pattern) (ha : d108112 q = 1) (hb : d141869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108112, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108112, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108113 q = 1) (hb : d141870 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108113, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108113, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108114 q = 1) (hb : d141871 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108114, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108114, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108115 q = 1) (hb : d141872 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108115, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108115, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108116 q = 1) (hb : d141873 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108116, d141873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108116, d141873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32111 (p : Pattern) (ha : d108121 p = 1) (hb : d141878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108087 q = 1) (hb : d141844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32103 q ha hb
    | true =>
      simp only [d108087, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108088 q = 1) (hb : d141845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108091 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32104 q ha hb
    | true =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108092 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108093 q = 1) (hb : d141850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108093, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108093, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108094 q = 1) (hb : d141851 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108094, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108094, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108120 q = 1) (hb : d141877 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108120, d141877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108120, d141877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108121 q = 1) (hb : d141878 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108121, d141878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108121, d141878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32112 (p : Pattern) (ha : d108123 p = 1) (hb : d141880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108091 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32104 q ha hb
    | true =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108092 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108097 q = 1) (hb : d141854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108097, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108097, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108098 q = 1) (hb : d141855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108098, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108098, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108122 q = 1) (hb : d141879 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108122, d141879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108122, d141879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108123 q = 1) (hb : d141880 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108123, d141880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108123, d141880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32113 (p : Pattern) (ha : d108130 p = 1) (hb : d141887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108087 q = 1) (hb : d141844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32103 q ha hb
    | true =>
      simp only [d108087, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108088 q = 1) (hb : d141845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108091 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32104 q ha hb
    | true =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108092 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108093 q = 1) (hb : d141850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108093, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108093, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108128 q = 1) (hb : d141885 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108128, d141885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108128, d141885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108129 q = 1) (hb : d141886 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108129, d141886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108129, d141886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108130 q = 1) (hb : d141887 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108130, d141887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108130, d141887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32114 (p : Pattern) (ha : d108133 p = 1) (hb : d141890 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108091 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32104 q ha hb
    | true =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108092 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108097 q = 1) (hb : d141854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108097, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108097, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108131 q = 1) (hb : d141888 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108131, d141888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108131, d141888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108132 q = 1) (hb : d141889 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108132, d141889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108132, d141889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108133 q = 1) (hb : d141890 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108133, d141890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108133, d141890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32115 (p : Pattern) (ha : d108142 p = 1) (hb : d141899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108137 q = 1) (hb : d141894 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108137, d141894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28809 q hb ha
    | true =>
      simp only [d108137, d141894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108138 q = 1) (hb : d141895 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108138, d141895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108138, d141895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108139 q = 1) (hb : d141896 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108139, d141896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108139, d141896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108077 q = 1) (hb : d114586 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108077, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22898 q hb ha
    | true =>
      simp only [d108077, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108078 q = 1) (hb : d114587 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108078, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108078, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108079 q = 1) (hb : d114588 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108079, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108079, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108140 q = 1) (hb : d141897 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108140, d141897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108140, d141897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88641 q = 1) (hb : d108080 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88641, d108080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10613 q ha hb
    | true =>
      simp only [d88641, d108080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d88642 q = 1) (hb : d108081 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88642, d108081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88642, d108081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88643 q = 1) (hb : d108082 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88643, d108082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88643, d108082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108083 q = 1) (hb : d141841 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108083, d141841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108083, d141841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d108141 q = 1) (hb : d141898 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108141, d141898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108141, d141898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108142 q = 1) (hb : d141899 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108142, d141899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108142, d141899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro32116 (p : Pattern) (ha : d108148 p = 1) (hb : d141905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108143 q = 1) (hb : d141900 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108143, d141900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32115 q ha hb
    | true =>
      simp only [d108143, d141900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108144 q = 1) (hb : d141901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108144, d141901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108144, d141901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108087 q = 1) (hb : d141844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32103 q ha hb
    | true =>
      simp only [d108087, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108088 q = 1) (hb : d141845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108145 q = 1) (hb : d141902 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108145, d141902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108145, d141902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108146 q = 1) (hb : d141903 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108146, d141903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108146, d141903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108147 q = 1) (hb : d141904 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108147, d141904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108147, d141904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108148 q = 1) (hb : d141905 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108148, d141905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108148, d141905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32117 (p : Pattern) (ha : d108156 p = 1) (hb : d141843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108077 q = 1) (hb : d114586 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108077, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22898 q hb ha
    | true =>
      simp only [d108077, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108078 q = 1) (hb : d114587 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108078, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108078, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108079 q = 1) (hb : d114588 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108079, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108079, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88641 q = 1) (hb : d108080 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88641, d108080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10613 q ha hb
    | true =>
      simp only [d88641, d108080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88642 q = 1) (hb : d108081 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88642, d108081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88642, d108081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88643 q = 1) (hb : d108082 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88643, d108082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88643, d108082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108083 q = 1) (hb : d141841 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108083, d141841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108083, d141841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d88641 q = 1) (hb : d108151 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88641, d108151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22901 q ha hb
    | true =>
      simp only [d88641, d108151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d88642 q = 1) (hb : d108152 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88642, d108152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88642, d108152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88643 q = 1) (hb : d108153 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88643, d108153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88643, d108153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d88644 q = 1) (hb : d108154 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88644, d108154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88644, d108154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108155 q = 1) (hb : d141842 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108155, d141842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108155, d141842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d108156 q = 1) (hb : d141843 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108156, d141843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108156, d141843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro32118 (p : Pattern) (ha : d108162 p = 1) (hb : d141911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108157 q = 1) (hb : d141844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108157, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32117 q ha hb
    | true =>
      simp only [d108157, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108158 q = 1) (hb : d141845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108158, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108158, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108159 q = 1) (hb : d141908 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108159, d141908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108159, d141908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108160 q = 1) (hb : d141909 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108160, d141909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108160, d141909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108161 q = 1) (hb : d141910 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108161, d141910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108161, d141910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108162 q = 1) (hb : d141911 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108162, d141911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108162, d141911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32119 (p : Pattern) (ha : d108168 p = 1) (hb : d141917 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108124 q = 1) (hb : d141881 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108124, d141881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32111 q ha hb
    | true =>
      simp only [d108124, d141881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32112 q ha hb
  have h2 (q : Pattern) (ha : d108125 q = 1) (hb : d141882 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108125, d141882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108125, d141882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108126 q = 1) (hb : d141883 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108126, d141883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108126, d141883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108127 q = 1) (hb : d141884 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108127, d141884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108127, d141884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108134 q = 1) (hb : d141891 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108134, d141891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32113 q ha hb
    | true =>
      simp only [d108134, d141891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32114 q ha hb
  have h6 (q : Pattern) (ha : d108135 q = 1) (hb : d141892 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108135, d141892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108135, d141892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108136 q = 1) (hb : d141893 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108136, d141893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108136, d141893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108149 q = 1) (hb : d141906 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108149, d141906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32116 q ha hb
    | true =>
      simp only [d108149, d141906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32105 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108101 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d108150 q = 1) (hb : d141907 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108150, d141907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108150, d141907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d108163 q = 1) (hb : d141912 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108163, d141912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32118 q ha hb
    | true =>
      simp only [d108163, d141912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108164 q = 1) (hb : d141913 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108164, d141913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108164, d141913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d108165 q = 1) (hb : d141914 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108165, d141914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108165, d141914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108166 q = 1) (hb : d141915 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108166, d141915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108166, d141915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108167 q = 1) (hb : d141916 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108167, d141916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108167, d141916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108168 q = 1) (hb : d141917 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108168, d141917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108168, d141917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro32120 (p : Pattern) (ha : d108169 p = 1) (hb : d141918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108087 q = 1) (hb : d141844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32103 q ha hb
    | true =>
      simp only [d108087, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108088 q = 1) (hb : d141845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108091 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32104 q ha hb
    | true =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108092 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108093 q = 1) (hb : d141850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108093, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108093, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108094 q = 1) (hb : d141851 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108094, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108094, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108120 q = 1) (hb : d141877 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108120, d141877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108120, d141877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108169 q = 1) (hb : d141918 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108169, d141918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108169, d141918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32121 (p : Pattern) (ha : d108170 p = 1) (hb : d141919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108091 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32104 q ha hb
    | true =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108092 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108097 q = 1) (hb : d141854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108097, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108097, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108098 q = 1) (hb : d141855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108098, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108098, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108122 q = 1) (hb : d141879 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108122, d141879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108122, d141879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108170 q = 1) (hb : d141919 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108170, d141919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108170, d141919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32122 (p : Pattern) (ha : d108175 p = 1) (hb : d141924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108087 q = 1) (hb : d141844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32103 q ha hb
    | true =>
      simp only [d108087, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108088 q = 1) (hb : d141845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108091 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32104 q ha hb
    | true =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108092 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108093 q = 1) (hb : d141850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108093, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108093, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108128 q = 1) (hb : d141885 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108128, d141885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108128, d141885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108129 q = 1) (hb : d141886 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108129, d141886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108129, d141886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108175 q = 1) (hb : d141924 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108175, d141924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108175, d141924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32123 (p : Pattern) (ha : d108176 p = 1) (hb : d141925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108091 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32104 q ha hb
    | true =>
      simp only [d108091, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108092 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108092, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108097 q = 1) (hb : d141854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108097, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108097, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108131 q = 1) (hb : d141888 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108131, d141888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108131, d141888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108132 q = 1) (hb : d141889 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108132, d141889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108132, d141889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108176 q = 1) (hb : d141925 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108176, d141925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108176, d141925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32124 (p : Pattern) (ha : d108180 p = 1) (hb : d141929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108143 q = 1) (hb : d141900 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108143, d141900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32115 q ha hb
    | true =>
      simp only [d108143, d141900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108144 q = 1) (hb : d141901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108144, d141901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108144, d141901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108087 q = 1) (hb : d141844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108087, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32103 q ha hb
    | true =>
      simp only [d108087, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108088 q = 1) (hb : d141845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108088, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108088, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108145 q = 1) (hb : d141902 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108145, d141902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108145, d141902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108146 q = 1) (hb : d141903 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108146, d141903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108146, d141903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108147 q = 1) (hb : d141904 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108147, d141904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108147, d141904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108180 q = 1) (hb : d141929 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108180, d141929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108180, d141929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32125 (p : Pattern) (ha : d108183 p = 1) (hb : d141932 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108157 q = 1) (hb : d141844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108157, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32117 q ha hb
    | true =>
      simp only [d108157, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108158 q = 1) (hb : d141845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108158, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108158, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108159 q = 1) (hb : d141908 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108159, d141908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108159, d141908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108160 q = 1) (hb : d141909 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108160, d141909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108160, d141909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108161 q = 1) (hb : d141910 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108161, d141910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108161, d141910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108183 q = 1) (hb : d141932 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108183, d141932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108183, d141932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32126 (p : Pattern) (ha : d108189 p = 1) (hb : d141938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108124 q = 1) (hb : d141881 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108124, d141881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32111 q ha hb
    | true =>
      simp only [d108124, d141881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32112 q ha hb
  have h2 (q : Pattern) (ha : d108125 q = 1) (hb : d141882 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108125, d141882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108125, d141882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108126 q = 1) (hb : d141883 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108126, d141883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108126, d141883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108127 q = 1) (hb : d141884 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108127, d141884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108127, d141884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108134 q = 1) (hb : d141891 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108134, d141891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32113 q ha hb
    | true =>
      simp only [d108134, d141891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32114 q ha hb
  have h6 (q : Pattern) (ha : d108135 q = 1) (hb : d141892 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108135, d141892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108135, d141892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108136 q = 1) (hb : d141893 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108136, d141893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108136, d141893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108149 q = 1) (hb : d141906 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108149, d141906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32116 q ha hb
    | true =>
      simp only [d108149, d141906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32105 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108101 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d108150 q = 1) (hb : d141907 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108150, d141907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108150, d141907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d108163 q = 1) (hb : d141912 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108163, d141912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32118 q ha hb
    | true =>
      simp only [d108163, d141912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108164 q = 1) (hb : d141913 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108164, d141913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108164, d141913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d108165 q = 1) (hb : d141914 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108165, d141914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108165, d141914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108166 q = 1) (hb : d141915 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108166, d141915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108166, d141915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108167 q = 1) (hb : d141916 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108167, d141916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108167, d141916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108171 q = 1) (hb : d141920 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108171, d141920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32120 q ha hb
    | true =>
      simp only [d108171, d141920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32121 q ha hb
  have h17 (q : Pattern) (ha : d108172 q = 1) (hb : d141921 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108172, d141921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108172, d141921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108173 q = 1) (hb : d141922 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108173, d141922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108173, d141922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d108174 q = 1) (hb : d141923 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108174, d141923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108174, d141923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108177 q = 1) (hb : d141926 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108177, d141926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32122 q ha hb
    | true =>
      simp only [d108177, d141926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32123 q ha hb
  have h21 (q : Pattern) (ha : d108178 q = 1) (hb : d141927 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108178, d141927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108178, d141927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d108179 q = 1) (hb : d141928 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108179, d141928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108179, d141928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d108181 q = 1) (hb : d141930 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108181, d141930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32124 q ha hb
    | true =>
      simp only [d108181, d141930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32108 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d108111 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d108182 q = 1) (hb : d141931 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108182, d141931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108182, d141931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d108184 q = 1) (hb : d141933 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108184, d141933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32125 q ha hb
    | true =>
      simp only [d108184, d141933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d108185 q = 1) (hb : d141934 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108185, d141934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d108185, d141934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d108186 q = 1) (hb : d141935 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108186, d141935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d108186, d141935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108187 q = 1) (hb : d141936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108187, d141936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108187, d141936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d108188 q = 1) (hb : d141937 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108188, d141937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108188, d141937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d108189 q = 1) (hb : d141938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108189, d141938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108189, d141938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro32127 (p : Pattern) (ha : d108196 p = 1) (hb : d141945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108101 q = 1) (hb : d141858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108101, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32105 q ha hb
    | true =>
      simp only [d108101, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32106 q ha hb
  have h2 (q : Pattern) (ha : d108102 q = 1) (hb : d141859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108102, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108102, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108103 q = 1) (hb : d141860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108103, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108103, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108104 q = 1) (hb : d141861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108104, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108104, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108105 q = 1) (hb : d141862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108105, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108105, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108191 q = 1) (hb : d141940 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108191, d141940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32106 q ha hb
    | true =>
      simp only [d108191, d141940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108192 q = 1) (hb : d141941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108192, d141941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108192, d141941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108193 q = 1) (hb : d141942 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108193, d141942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108193, d141942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108194 q = 1) (hb : d141943 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108194, d141943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108194, d141943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108195 q = 1) (hb : d141944 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108195, d141944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108195, d141944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108196 q = 1) (hb : d141945 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108196, d141945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108196, d141945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32128 (p : Pattern) (ha : d108202 p = 1) (hb : d141951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108191 q = 1) (hb : d141940 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108191, d141940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32106 q ha hb
    | true =>
      simp only [d108191, d141940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108192 q = 1) (hb : d141941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108192, d141941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108192, d141941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108193 q = 1) (hb : d141942 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108193, d141942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108193, d141942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108194 q = 1) (hb : d141943 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108194, d141943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108194, d141943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108195 q = 1) (hb : d141944 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108195, d141944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108195, d141944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108197 q = 1) (hb : d141946 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108197, d141946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32109 q ha hb
    | true =>
      simp only [d108197, d141946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108198 q = 1) (hb : d141947 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108198, d141947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108198, d141947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108199 q = 1) (hb : d141948 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108199, d141948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108199, d141948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108200 q = 1) (hb : d141949 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108200, d141949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108200, d141949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108201 q = 1) (hb : d141950 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108201, d141950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108201, d141950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108202 q = 1) (hb : d141951 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108202, d141951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108202, d141951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32129 (p : Pattern) (ha : d108209 p = 1) (hb : d141958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108181 q = 1) (hb : d141930 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108181, d141930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32124 q ha hb
    | true =>
      simp only [d108181, d141930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32108 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108111 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108182 q = 1) (hb : d141931 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108182, d141931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108182, d141931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108184 q = 1) (hb : d141933 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108184, d141933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32125 q ha hb
    | true =>
      simp only [d108184, d141933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108185 q = 1) (hb : d141934 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108185, d141934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108185, d141934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108186 q = 1) (hb : d141935 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108186, d141935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108186, d141935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108207 q = 1) (hb : d141956 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108207, d141956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108207, d141956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108208 q = 1) (hb : d141957 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108208, d141957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108208, d141957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108209 q = 1) (hb : d141958 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108209, d141958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108209, d141958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32130 (p : Pattern) (ha : d108211 p = 1) (hb : d141960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108197 q = 1) (hb : d141946 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108197, d141946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32109 q ha hb
    | true =>
      simp only [d108197, d141946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108198 q = 1) (hb : d141947 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108198, d141947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108198, d141947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108199 q = 1) (hb : d141948 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108199, d141948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108199, d141948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108200 q = 1) (hb : d141949 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108200, d141949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108200, d141949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108201 q = 1) (hb : d141950 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108201, d141950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108201, d141950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108211 q = 1) (hb : d141960 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108211, d141960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108211, d141960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32131 (p : Pattern) (ha : d108229 p = 1) (hb : d141972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108217 q = 1) (hb : d141966 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108217, d141966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28826 q hb ha
    | true =>
      simp only [d108217, d141966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108218 q = 1) (hb : d141967 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108218, d141967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108218, d141967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108219 q = 1) (hb : d141968 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108219, d141968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108219, d141968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108220 q = 1) (hb : d114643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108220, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22912 q hb ha
    | true =>
      simp only [d108220, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108221 q = 1) (hb : d114644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108221, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108221, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108222 q = 1) (hb : d114645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108222, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108222, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108223 q = 1) (hb : d141969 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108223, d141969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108223, d141969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88705 q = 1) (hb : d108224 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88705, d108224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10632 q ha hb
    | true =>
      simp only [d88705, d108224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d88706 q = 1) (hb : d108225 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88706, d108225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88706, d108225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88707 q = 1) (hb : d108226 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88707, d108226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88707, d108226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108227 q = 1) (hb : d141970 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108227, d141970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108227, d141970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d108228 q = 1) (hb : d141971 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108228, d141971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108228, d141971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108229 q = 1) (hb : d141972 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108229, d141972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108229, d141972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro32132 (p : Pattern) (ha : d108234 p = 1) (hb : d141976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108220 q = 1) (hb : d114643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108220, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22912 q hb ha
    | true =>
      simp only [d108220, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108221 q = 1) (hb : d114644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108221, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108221, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108222 q = 1) (hb : d114645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108222, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108222, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88705 q = 1) (hb : d108224 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88705, d108224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10632 q ha hb
    | true =>
      simp only [d88705, d108224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88706 q = 1) (hb : d108225 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88706, d108225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88706, d108225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88707 q = 1) (hb : d108226 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88707, d108226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88707, d108226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108227 q = 1) (hb : d141970 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108227, d141970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108227, d141970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d88708 q = 1) (hb : d108232 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88708, d108232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d88708, d108232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d108233 q = 1) (hb : d141975 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108233, d141975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108233, d141975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108234 q = 1) (hb : d141976 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108234, d141976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108234, d141976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32133 (p : Pattern) (ha : d108240 p = 1) (hb : d141982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108230 q = 1) (hb : d141973 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108230, d141973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32131 q ha hb
    | true =>
      simp only [d108230, d141973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108231 q = 1) (hb : d141974 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108231, d141974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108231, d141974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108235 q = 1) (hb : d141977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108235, d141977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32132 q ha hb
    | true =>
      simp only [d108235, d141977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108236 q = 1) (hb : d141978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108236, d141978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108236, d141978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108237 q = 1) (hb : d141979 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108237, d141979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108237, d141979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108238 q = 1) (hb : d141980 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108238, d141980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108238, d141980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108239 q = 1) (hb : d141981 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108239, d141981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108239, d141981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108240 q = 1) (hb : d141982 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108240, d141982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108240, d141982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32134 (p : Pattern) (ha : d108242 p = 1) (hb : d141984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88705 q = 1) (hb : d108224 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88705, d108224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10632 q ha hb
    | true =>
      simp only [d88705, d108224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d88706 q = 1) (hb : d108225 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88706, d108225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88706, d108225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d88707 q = 1) (hb : d108226 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88707, d108226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88707, d108226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88708 q = 1) (hb : d108232 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88708, d108232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88708, d108232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108241 q = 1) (hb : d141983 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108241, d141983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108241, d141983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108242 q = 1) (hb : d141984 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108242, d141984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108242, d141984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32135 (p : Pattern) (ha : d108248 p = 1) (hb : d141990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108235 q = 1) (hb : d141977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108235, d141977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32132 q ha hb
    | true =>
      simp only [d108235, d141977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108236 q = 1) (hb : d141978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108236, d141978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108236, d141978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108243 q = 1) (hb : d141985 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108243, d141985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32134 q ha hb
    | true =>
      simp only [d108243, d141985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108244 q = 1) (hb : d141986 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108244, d141986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108244, d141986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108245 q = 1) (hb : d141987 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108245, d141987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108245, d141987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108246 q = 1) (hb : d141988 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108246, d141988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108246, d141988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108247 q = 1) (hb : d141989 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108247, d141989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108247, d141989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108248 q = 1) (hb : d141990 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108248, d141990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108248, d141990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32136 (p : Pattern) (ha : d108261 p = 1) (hb : d141976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108220 q = 1) (hb : d114643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108220, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22912 q hb ha
    | true =>
      simp only [d108220, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108221 q = 1) (hb : d114644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108221, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108221, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108222 q = 1) (hb : d114645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108222, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108222, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88705 q = 1) (hb : d108224 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88705, d108224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10632 q ha hb
    | true =>
      simp only [d88705, d108224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88706 q = 1) (hb : d108225 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88706, d108225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88706, d108225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88707 q = 1) (hb : d108226 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88707, d108226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88707, d108226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108227 q = 1) (hb : d141970 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108227, d141970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108227, d141970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d88705 q = 1) (hb : d108256 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88705, d108256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22917 q ha hb
    | true =>
      simp only [d88705, d108256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d88706 q = 1) (hb : d108257 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88706, d108257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88706, d108257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88707 q = 1) (hb : d108258 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88707, d108258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88707, d108258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d88708 q = 1) (hb : d108259 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88708, d108259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88708, d108259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108260 q = 1) (hb : d141975 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108260, d141975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108260, d141975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d108261 q = 1) (hb : d141976 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108261, d141976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108261, d141976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro32137 (p : Pattern) (ha : d108267 p = 1) (hb : d141996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108262 q = 1) (hb : d141977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108262, d141977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32136 q ha hb
    | true =>
      simp only [d108262, d141977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108263 q = 1) (hb : d141978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108263, d141978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108263, d141978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108264 q = 1) (hb : d141993 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108264, d141993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108264, d141993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108265 q = 1) (hb : d141994 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108265, d141994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108265, d141994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108266 q = 1) (hb : d141995 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108266, d141995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108266, d141995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108267 q = 1) (hb : d141996 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108267, d141996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108267, d141996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32138 (p : Pattern) (ha : d108273 p = 1) (hb : d142002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108249 q = 1) (hb : d141991 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108249, d141991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32133 q ha hb
    | true =>
      simp only [d108249, d141991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32135 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108254 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108255 q = 1) (hb : d141992 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108255, d141992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108255, d141992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108268 q = 1) (hb : d141997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108268, d141997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32137 q ha hb
    | true =>
      simp only [d108268, d141997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108269 q = 1) (hb : d141998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108269, d141998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108269, d141998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108270 q = 1) (hb : d141999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108270, d141999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108270, d141999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108271 q = 1) (hb : d142000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108271, d142000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108271, d142000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108272 q = 1) (hb : d142001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108272, d142001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108272, d142001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108273 q = 1) (hb : d142002 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108273, d142002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108273, d142002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32139 (p : Pattern) (ha : d108253 p = 1) (hb : d142007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108243 q = 1) (hb : d141985 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108243, d141985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32134 q ha hb
    | true =>
      simp only [d108243, d141985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108244 q = 1) (hb : d141986 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108244, d141986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108244, d141986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108250 q = 1) (hb : d142004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108250, d142004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108250, d142004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108251 q = 1) (hb : d142005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108251, d142005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108251, d142005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108252 q = 1) (hb : d142006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108252, d142006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108252, d142006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108253 q = 1) (hb : d142007 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108253, d142007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108253, d142007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32140 (p : Pattern) (ha : d108280 p = 1) (hb : d142013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108275 q = 1) (hb : d142008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108275, d142008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32139 q ha hb
    | true =>
      simp only [d108275, d142008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108276 q = 1) (hb : d142009 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108276, d142009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108276, d142009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108277 q = 1) (hb : d142010 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108277, d142010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108277, d142010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108278 q = 1) (hb : d142011 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108278, d142011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108278, d142011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108279 q = 1) (hb : d142012 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108279, d142012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108279, d142012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108280 q = 1) (hb : d142013 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108280, d142013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108280, d142013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32141 (p : Pattern) (ha : d108286 p = 1) (hb : d142019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108107 q = 1) (hb : d141864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108107, d141864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108107, d141864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32107 q ha hb
  have h2 (q : Pattern) (ha : d108108 q = 1) (hb : d141865 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108108, d141865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108108, d141865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108117 q = 1) (hb : d141874 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108117, d141874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32107 q ha hb
    | true =>
      simp only [d108117, d141874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32110 q ha hb
  have h4 (q : Pattern) (ha : d108118 q = 1) (hb : d141875 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108118, d141875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108118, d141875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108119 q = 1) (hb : d141876 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108119, d141876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108119, d141876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108190 q = 1) (hb : d141939 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108190, d141939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32119 q ha hb
    | true =>
      simp only [d108190, d141939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32126 q ha hb
  have h7 (q : Pattern) (ha : d108203 q = 1) (hb : d141952 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108203, d141952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32127 q ha hb
    | true =>
      simp only [d108203, d141952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32128 q ha hb
  have h8 (q : Pattern) (ha : d108204 q = 1) (hb : d141953 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108204, d141953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108204, d141953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108205 q = 1) (hb : d141954 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108205, d141954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108205, d141954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d108206 q = 1) (hb : d141955 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108206, d141955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108206, d141955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108210 q = 1) (hb : d141959 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108210, d141959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108210, d141959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32129 q ha hb
  have h12 (q : Pattern) (ha : d108212 q = 1) (hb : d141961 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108212, d141961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108212, d141961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32130 q ha hb
  have h13 (q : Pattern) (ha : d108213 q = 1) (hb : d141962 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108213, d141962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108213, d141962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108214 q = 1) (hb : d141963 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108214, d141963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108214, d141963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d108215 q = 1) (hb : d141964 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108215, d141964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108215, d141964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d108216 q = 1) (hb : d141965 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108216, d141965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108216, d141965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108274 q = 1) (hb : d142003 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108274, d142003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108274, d142003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32138 q ha hb
  have h18 (q : Pattern) (ha : d108281 q = 1) (hb : d142014 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108281, d142014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108281, d142014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32140 q ha hb
  have h19 (q : Pattern) (ha : d108282 q = 1) (hb : d142015 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108282, d142015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108282, d142015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108283 q = 1) (hb : d142016 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108283, d142016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108283, d142016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d108284 q = 1) (hb : d142017 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108284, d142017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108284, d142017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d108285 q = 1) (hb : d142018 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108285, d142018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108285, d142018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d108286 q = 1) (hb : d142019 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108286, d142019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108286, d142019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro32142 (p : Pattern) (ha : d108292 p = 1) (hb : d142025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108287 q = 1) (hb : d142020 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108287, d142020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108287, d142020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32141 q ha hb
  have h2 (q : Pattern) (ha : d108288 q = 1) (hb : d142021 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108288, d142021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108288, d142021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108289 q = 1) (hb : d142022 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108289, d142022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108289, d142022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108290 q = 1) (hb : d142023 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108290, d142023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108290, d142023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108291 q = 1) (hb : d142024 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108291, d142024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108291, d142024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108292 q = 1) (hb : d142025 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108292, d142025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108292, d142025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32143 (p : Pattern) (ha : d108305 p = 1) (hb : d142031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108296 q = 1) (hb : d114730 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108296, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22930 q hb ha
    | true =>
      simp only [d108296, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108297 q = 1) (hb : d114731 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108297, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108297, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108298 q = 1) (hb : d114732 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108298, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108298, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88794 q = 1) (hb : d108299 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88794, d108299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10645 q ha hb
    | true =>
      simp only [d88794, d108299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88795 q = 1) (hb : d108300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88795, d108300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88795, d108300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88796 q = 1) (hb : d108301 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88796, d108301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88796, d108301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108302 q = 1) (hb : d142029 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108302, d142029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108302, d142029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d88797 q = 1) (hb : d108303 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88797, d108303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d88797, d108303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d108304 q = 1) (hb : d142030 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108304, d142030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108304, d142030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108305 q = 1) (hb : d142031 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108305, d142031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108305, d142031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32144 (p : Pattern) (ha : d108309 p = 1) (hb : d142035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88794 q = 1) (hb : d108299 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88794, d108299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10645 q ha hb
    | true =>
      simp only [d88794, d108299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d88795 q = 1) (hb : d108300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88795, d108300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88795, d108300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d88796 q = 1) (hb : d108301 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88796, d108301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88796, d108301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88797 q = 1) (hb : d108303 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88797, d108303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88797, d108303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108308 q = 1) (hb : d142034 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108308, d142034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108308, d142034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108309 q = 1) (hb : d142035 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108309, d142035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108309, d142035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32145 (p : Pattern) (ha : d108315 p = 1) (hb : d142041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108306 q = 1) (hb : d142032 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108306, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32143 q ha hb
    | true =>
      simp only [d108306, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108307 q = 1) (hb : d142033 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108307, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108307, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108310 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32144 q ha hb
    | true =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108311 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108312 q = 1) (hb : d142038 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108312, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108312, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108313 q = 1) (hb : d142039 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108313, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108313, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108314 q = 1) (hb : d142040 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108314, d142040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108314, d142040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108315 q = 1) (hb : d142041 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108315, d142041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108315, d142041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32146 (p : Pattern) (ha : d108319 p = 1) (hb : d142045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108310 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32144 q ha hb
    | true =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108311 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108316 q = 1) (hb : d142042 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108316, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108316, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108317 q = 1) (hb : d142043 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108317, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108317, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108318 q = 1) (hb : d142044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108318, d142044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108318, d142044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108319 q = 1) (hb : d142045 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108319, d142045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108319, d142045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32147 (p : Pattern) (ha : d108325 p = 1) (hb : d142051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108320 q = 1) (hb : d142046 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108320, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32145 q ha hb
    | true =>
      simp only [d108320, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32146 q ha hb
  have h2 (q : Pattern) (ha : d108321 q = 1) (hb : d142047 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108321, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108321, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108322 q = 1) (hb : d142048 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108322, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108322, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108323 q = 1) (hb : d142049 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108323, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108323, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108324 q = 1) (hb : d142050 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108324, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108324, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108325 q = 1) (hb : d142051 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108325, d142051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108325, d142051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32148 (p : Pattern) (ha : d108328 p = 1) (hb : d142054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108306 q = 1) (hb : d142032 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108306, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32143 q ha hb
    | true =>
      simp only [d108306, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108307 q = 1) (hb : d142033 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108307, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108307, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108310 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32144 q ha hb
    | true =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108311 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108312 q = 1) (hb : d142038 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108312, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108312, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108313 q = 1) (hb : d142039 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108313, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108313, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108314 q = 1) (hb : d142040 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108314, d142040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108314, d142040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108328 q = 1) (hb : d142054 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108328, d142054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108328, d142054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32149 (p : Pattern) (ha : d108329 p = 1) (hb : d142055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108310 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32144 q ha hb
    | true =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108311 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108316 q = 1) (hb : d142042 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108316, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108316, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108317 q = 1) (hb : d142043 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108317, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108317, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108318 q = 1) (hb : d142044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108318, d142044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108318, d142044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108329 q = 1) (hb : d142055 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108329, d142055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108329, d142055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32150 (p : Pattern) (ha : d108335 p = 1) (hb : d142061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108320 q = 1) (hb : d142046 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108320, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32145 q ha hb
    | true =>
      simp only [d108320, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32146 q ha hb
  have h2 (q : Pattern) (ha : d108321 q = 1) (hb : d142047 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108321, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108321, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108322 q = 1) (hb : d142048 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108322, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108322, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108323 q = 1) (hb : d142049 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108323, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108323, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108324 q = 1) (hb : d142050 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108324, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108324, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108330 q = 1) (hb : d142056 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108330, d142056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32148 q ha hb
    | true =>
      simp only [d108330, d142056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32149 q ha hb
  have h7 (q : Pattern) (ha : d108331 q = 1) (hb : d142057 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108331, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108331, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108332 q = 1) (hb : d142058 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108332, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108332, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108333 q = 1) (hb : d142059 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108333, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108333, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108334 q = 1) (hb : d142060 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108334, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108334, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108335 q = 1) (hb : d142061 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108335, d142061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108335, d142061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32151 (p : Pattern) (ha : d108340 p = 1) (hb : d142066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108306 q = 1) (hb : d142032 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108306, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32143 q ha hb
    | true =>
      simp only [d108306, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108307 q = 1) (hb : d142033 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108307, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108307, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108310 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32144 q ha hb
    | true =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108311 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108312 q = 1) (hb : d142038 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108312, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108312, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108313 q = 1) (hb : d142039 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108313, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108313, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108339 q = 1) (hb : d142065 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108339, d142065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108339, d142065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108340 q = 1) (hb : d142066 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108340, d142066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108340, d142066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32152 (p : Pattern) (ha : d108342 p = 1) (hb : d142068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108310 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32144 q ha hb
    | true =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108311 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108316 q = 1) (hb : d142042 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108316, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108316, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108317 q = 1) (hb : d142043 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108317, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108317, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108341 q = 1) (hb : d142067 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108341, d142067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108341, d142067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108342 q = 1) (hb : d142068 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108342, d142068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108342, d142068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32153 (p : Pattern) (ha : d108349 p = 1) (hb : d142075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108306 q = 1) (hb : d142032 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108306, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32143 q ha hb
    | true =>
      simp only [d108306, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108307 q = 1) (hb : d142033 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108307, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108307, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108310 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32144 q ha hb
    | true =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108311 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108312 q = 1) (hb : d142038 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108312, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108312, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108347 q = 1) (hb : d142073 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108347, d142073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108347, d142073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108348 q = 1) (hb : d142074 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108348, d142074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108348, d142074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108349 q = 1) (hb : d142075 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108349, d142075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108349, d142075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32154 (p : Pattern) (ha : d108352 p = 1) (hb : d142078 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108310 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32144 q ha hb
    | true =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108311 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108316 q = 1) (hb : d142042 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108316, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108316, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108350 q = 1) (hb : d142076 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108350, d142076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108350, d142076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108351 q = 1) (hb : d142077 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108351, d142077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108351, d142077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108352 q = 1) (hb : d142078 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108352, d142078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108352, d142078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32155 (p : Pattern) (ha : d108361 p = 1) (hb : d142087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108356 q = 1) (hb : d142082 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108356, d142082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28855 q hb ha
    | true =>
      simp only [d108356, d142082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108357 q = 1) (hb : d142083 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108357, d142083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108357, d142083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108358 q = 1) (hb : d142084 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108358, d142084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108358, d142084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108296 q = 1) (hb : d114730 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108296, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22930 q hb ha
    | true =>
      simp only [d108296, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108297 q = 1) (hb : d114731 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108297, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108297, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108298 q = 1) (hb : d114732 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108298, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108298, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108359 q = 1) (hb : d142085 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108359, d142085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108359, d142085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88794 q = 1) (hb : d108299 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88794, d108299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10645 q ha hb
    | true =>
      simp only [d88794, d108299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d88795 q = 1) (hb : d108300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88795, d108300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88795, d108300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88796 q = 1) (hb : d108301 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88796, d108301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88796, d108301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108302 q = 1) (hb : d142029 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108302, d142029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108302, d142029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d108360 q = 1) (hb : d142086 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108360, d142086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108360, d142086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108361 q = 1) (hb : d142087 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108361, d142087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108361, d142087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro32156 (p : Pattern) (ha : d108367 p = 1) (hb : d142093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108362 q = 1) (hb : d142088 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108362, d142088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32155 q ha hb
    | true =>
      simp only [d108362, d142088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108363 q = 1) (hb : d142089 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108363, d142089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108363, d142089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108306 q = 1) (hb : d142032 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108306, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32143 q ha hb
    | true =>
      simp only [d108306, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108307 q = 1) (hb : d142033 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108307, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108307, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108364 q = 1) (hb : d142090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108364, d142090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108364, d142090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108365 q = 1) (hb : d142091 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108365, d142091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108365, d142091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108366 q = 1) (hb : d142092 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108366, d142092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108366, d142092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108367 q = 1) (hb : d142093 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108367, d142093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108367, d142093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32157 (p : Pattern) (ha : d108375 p = 1) (hb : d142031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108296 q = 1) (hb : d114730 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108296, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22930 q hb ha
    | true =>
      simp only [d108296, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108297 q = 1) (hb : d114731 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108297, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108297, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108298 q = 1) (hb : d114732 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108298, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108298, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88794 q = 1) (hb : d108299 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88794, d108299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10645 q ha hb
    | true =>
      simp only [d88794, d108299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88795 q = 1) (hb : d108300 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88795, d108300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88795, d108300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88796 q = 1) (hb : d108301 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88796, d108301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88796, d108301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108302 q = 1) (hb : d142029 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108302, d142029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108302, d142029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d88794 q = 1) (hb : d108370 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88794, d108370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22933 q ha hb
    | true =>
      simp only [d88794, d108370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d88795 q = 1) (hb : d108371 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88795, d108371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88795, d108371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88796 q = 1) (hb : d108372 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88796, d108372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88796, d108372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d88797 q = 1) (hb : d108373 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88797, d108373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88797, d108373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108374 q = 1) (hb : d142030 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108374, d142030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108374, d142030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d108375 q = 1) (hb : d142031 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108375, d142031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108375, d142031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro32158 (p : Pattern) (ha : d108381 p = 1) (hb : d142099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108376 q = 1) (hb : d142032 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108376, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32157 q ha hb
    | true =>
      simp only [d108376, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108377 q = 1) (hb : d142033 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108377, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108377, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108378 q = 1) (hb : d142096 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108378, d142096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108378, d142096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108379 q = 1) (hb : d142097 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108379, d142097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108379, d142097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108380 q = 1) (hb : d142098 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108380, d142098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108380, d142098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108381 q = 1) (hb : d142099 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108381, d142099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108381, d142099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32159 (p : Pattern) (ha : d108387 p = 1) (hb : d142105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108343 q = 1) (hb : d142069 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108343, d142069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32151 q ha hb
    | true =>
      simp only [d108343, d142069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32152 q ha hb
  have h2 (q : Pattern) (ha : d108344 q = 1) (hb : d142070 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108344, d142070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108344, d142070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108345 q = 1) (hb : d142071 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108345, d142071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108345, d142071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108346 q = 1) (hb : d142072 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108346, d142072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108346, d142072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108353 q = 1) (hb : d142079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108353, d142079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32153 q ha hb
    | true =>
      simp only [d108353, d142079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32154 q ha hb
  have h6 (q : Pattern) (ha : d108354 q = 1) (hb : d142080 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108354, d142080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108354, d142080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108355 q = 1) (hb : d142081 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108355, d142081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108355, d142081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108368 q = 1) (hb : d142094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108368, d142094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32156 q ha hb
    | true =>
      simp only [d108368, d142094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32145 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108320 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d108369 q = 1) (hb : d142095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108369, d142095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108369, d142095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d108382 q = 1) (hb : d142100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108382, d142100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32158 q ha hb
    | true =>
      simp only [d108382, d142100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108383 q = 1) (hb : d142101 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108383, d142101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108383, d142101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d108384 q = 1) (hb : d142102 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108384, d142102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108384, d142102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108385 q = 1) (hb : d142103 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108385, d142103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108385, d142103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108386 q = 1) (hb : d142104 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108386, d142104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108386, d142104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108387 q = 1) (hb : d142105 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108387, d142105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108387, d142105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro32160 (p : Pattern) (ha : d108388 p = 1) (hb : d142106 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108306 q = 1) (hb : d142032 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108306, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32143 q ha hb
    | true =>
      simp only [d108306, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108307 q = 1) (hb : d142033 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108307, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108307, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108310 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32144 q ha hb
    | true =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108311 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108312 q = 1) (hb : d142038 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108312, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108312, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108313 q = 1) (hb : d142039 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108313, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108313, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108339 q = 1) (hb : d142065 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108339, d142065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108339, d142065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108388 q = 1) (hb : d142106 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108388, d142106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108388, d142106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32161 (p : Pattern) (ha : d108389 p = 1) (hb : d142107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108310 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32144 q ha hb
    | true =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108311 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108316 q = 1) (hb : d142042 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108316, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108316, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108317 q = 1) (hb : d142043 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108317, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108317, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108341 q = 1) (hb : d142067 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108341, d142067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108341, d142067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108389 q = 1) (hb : d142107 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108389, d142107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108389, d142107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32162 (p : Pattern) (ha : d108394 p = 1) (hb : d142112 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108306 q = 1) (hb : d142032 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108306, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32143 q ha hb
    | true =>
      simp only [d108306, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108307 q = 1) (hb : d142033 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108307, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108307, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108310 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32144 q ha hb
    | true =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108311 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108312 q = 1) (hb : d142038 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108312, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108312, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108347 q = 1) (hb : d142073 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108347, d142073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108347, d142073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108348 q = 1) (hb : d142074 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108348, d142074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108348, d142074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108394 q = 1) (hb : d142112 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108394, d142112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108394, d142112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32163 (p : Pattern) (ha : d108395 p = 1) (hb : d142113 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108310 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32144 q ha hb
    | true =>
      simp only [d108310, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108311 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108311, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108316 q = 1) (hb : d142042 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108316, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108316, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108350 q = 1) (hb : d142076 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108350, d142076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108350, d142076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108351 q = 1) (hb : d142077 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108351, d142077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108351, d142077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108395 q = 1) (hb : d142113 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108395, d142113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108395, d142113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32164 (p : Pattern) (ha : d108399 p = 1) (hb : d142117 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108362 q = 1) (hb : d142088 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108362, d142088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32155 q ha hb
    | true =>
      simp only [d108362, d142088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108363 q = 1) (hb : d142089 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108363, d142089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108363, d142089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108306 q = 1) (hb : d142032 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108306, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32143 q ha hb
    | true =>
      simp only [d108306, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108307 q = 1) (hb : d142033 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108307, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108307, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108364 q = 1) (hb : d142090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108364, d142090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108364, d142090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108365 q = 1) (hb : d142091 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108365, d142091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108365, d142091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108366 q = 1) (hb : d142092 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108366, d142092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108366, d142092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108399 q = 1) (hb : d142117 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108399, d142117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108399, d142117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32165 (p : Pattern) (ha : d108402 p = 1) (hb : d142120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108376 q = 1) (hb : d142032 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108376, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32157 q ha hb
    | true =>
      simp only [d108376, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108377 q = 1) (hb : d142033 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108377, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108377, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108378 q = 1) (hb : d142096 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108378, d142096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108378, d142096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108379 q = 1) (hb : d142097 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108379, d142097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108379, d142097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108380 q = 1) (hb : d142098 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108380, d142098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108380, d142098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108402 q = 1) (hb : d142120 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108402, d142120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108402, d142120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32166 (p : Pattern) (ha : d108408 p = 1) (hb : d142126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108343 q = 1) (hb : d142069 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108343, d142069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32151 q ha hb
    | true =>
      simp only [d108343, d142069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32152 q ha hb
  have h2 (q : Pattern) (ha : d108344 q = 1) (hb : d142070 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108344, d142070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108344, d142070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108345 q = 1) (hb : d142071 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108345, d142071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108345, d142071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108346 q = 1) (hb : d142072 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108346, d142072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108346, d142072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108353 q = 1) (hb : d142079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108353, d142079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32153 q ha hb
    | true =>
      simp only [d108353, d142079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32154 q ha hb
  have h6 (q : Pattern) (ha : d108354 q = 1) (hb : d142080 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108354, d142080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108354, d142080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108355 q = 1) (hb : d142081 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108355, d142081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108355, d142081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108368 q = 1) (hb : d142094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108368, d142094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32156 q ha hb
    | true =>
      simp only [d108368, d142094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32145 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108320 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d108369 q = 1) (hb : d142095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108369, d142095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108369, d142095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d108382 q = 1) (hb : d142100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108382, d142100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32158 q ha hb
    | true =>
      simp only [d108382, d142100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108383 q = 1) (hb : d142101 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108383, d142101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108383, d142101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d108384 q = 1) (hb : d142102 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108384, d142102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108384, d142102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108385 q = 1) (hb : d142103 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108385, d142103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108385, d142103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108386 q = 1) (hb : d142104 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108386, d142104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108386, d142104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108390 q = 1) (hb : d142108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108390, d142108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32160 q ha hb
    | true =>
      simp only [d108390, d142108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32161 q ha hb
  have h17 (q : Pattern) (ha : d108391 q = 1) (hb : d142109 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108391, d142109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108391, d142109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108392 q = 1) (hb : d142110 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108392, d142110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108392, d142110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d108393 q = 1) (hb : d142111 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108393, d142111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108393, d142111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108396 q = 1) (hb : d142114 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108396, d142114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32162 q ha hb
    | true =>
      simp only [d108396, d142114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32163 q ha hb
  have h21 (q : Pattern) (ha : d108397 q = 1) (hb : d142115 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108397, d142115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108397, d142115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d108398 q = 1) (hb : d142116 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108398, d142116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108398, d142116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d108400 q = 1) (hb : d142118 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108400, d142118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32164 q ha hb
    | true =>
      simp only [d108400, d142118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32148 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d108330 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d108401 q = 1) (hb : d142119 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108401, d142119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108401, d142119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d108403 q = 1) (hb : d142121 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108403, d142121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32165 q ha hb
    | true =>
      simp only [d108403, d142121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d108404 q = 1) (hb : d142122 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108404, d142122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d108404, d142122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d108405 q = 1) (hb : d142123 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108405, d142123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d108405, d142123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108406 q = 1) (hb : d142124 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108406, d142124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108406, d142124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d108407 q = 1) (hb : d142125 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108407, d142125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108407, d142125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d108408 q = 1) (hb : d142126 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108408, d142126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108408, d142126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro32167 (p : Pattern) (ha : d108415 p = 1) (hb : d142133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108320 q = 1) (hb : d142046 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108320, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32145 q ha hb
    | true =>
      simp only [d108320, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32146 q ha hb
  have h2 (q : Pattern) (ha : d108321 q = 1) (hb : d142047 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108321, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108321, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108322 q = 1) (hb : d142048 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108322, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108322, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108323 q = 1) (hb : d142049 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108323, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108323, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108324 q = 1) (hb : d142050 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108324, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108324, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108410 q = 1) (hb : d142128 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108410, d142128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32146 q ha hb
    | true =>
      simp only [d108410, d142128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108411 q = 1) (hb : d142129 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108411, d142129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108411, d142129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108412 q = 1) (hb : d142130 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108412, d142130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108412, d142130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108413 q = 1) (hb : d142131 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108413, d142131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108413, d142131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108414 q = 1) (hb : d142132 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108414, d142132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108414, d142132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108415 q = 1) (hb : d142133 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108415, d142133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108415, d142133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32168 (p : Pattern) (ha : d108421 p = 1) (hb : d142139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108410 q = 1) (hb : d142128 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108410, d142128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32146 q ha hb
    | true =>
      simp only [d108410, d142128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108411 q = 1) (hb : d142129 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108411, d142129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108411, d142129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108412 q = 1) (hb : d142130 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108412, d142130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108412, d142130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108413 q = 1) (hb : d142131 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108413, d142131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108413, d142131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108414 q = 1) (hb : d142132 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108414, d142132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108414, d142132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108416 q = 1) (hb : d142134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108416, d142134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32149 q ha hb
    | true =>
      simp only [d108416, d142134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108417 q = 1) (hb : d142135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108417, d142135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108417, d142135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108418 q = 1) (hb : d142136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108418, d142136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108418, d142136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108419 q = 1) (hb : d142137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108419, d142137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108419, d142137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108420 q = 1) (hb : d142138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108420, d142138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108420, d142138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108421 q = 1) (hb : d142139 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108421, d142139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108421, d142139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32169 (p : Pattern) (ha : d108428 p = 1) (hb : d142146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108400 q = 1) (hb : d142118 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108400, d142118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32164 q ha hb
    | true =>
      simp only [d108400, d142118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32148 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108330 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108401 q = 1) (hb : d142119 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108401, d142119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108401, d142119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108403 q = 1) (hb : d142121 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108403, d142121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32165 q ha hb
    | true =>
      simp only [d108403, d142121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108404 q = 1) (hb : d142122 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108404, d142122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108404, d142122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108405 q = 1) (hb : d142123 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108405, d142123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108405, d142123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108426 q = 1) (hb : d142144 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108426, d142144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108426, d142144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108427 q = 1) (hb : d142145 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108427, d142145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108427, d142145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108428 q = 1) (hb : d142146 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108428, d142146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108428, d142146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32170 (p : Pattern) (ha : d108430 p = 1) (hb : d142148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108416 q = 1) (hb : d142134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108416, d142134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32149 q ha hb
    | true =>
      simp only [d108416, d142134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108417 q = 1) (hb : d142135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108417, d142135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108417, d142135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108418 q = 1) (hb : d142136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108418, d142136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108418, d142136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108419 q = 1) (hb : d142137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108419, d142137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108419, d142137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108420 q = 1) (hb : d142138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108420, d142138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108420, d142138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108430 q = 1) (hb : d142148 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108430, d142148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108430, d142148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32171 (p : Pattern) (ha : d108448 p = 1) (hb : d142160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108436 q = 1) (hb : d142154 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108436, d142154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28872 q hb ha
    | true =>
      simp only [d108436, d142154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108437 q = 1) (hb : d142155 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108437, d142155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108437, d142155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108438 q = 1) (hb : d142156 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108438, d142156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108438, d142156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108439 q = 1) (hb : d114787 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108439, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22944 q hb ha
    | true =>
      simp only [d108439, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108440 q = 1) (hb : d114788 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108440, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108440, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108441 q = 1) (hb : d114789 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108441, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108441, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108442 q = 1) (hb : d142157 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108442, d142157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108442, d142157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88858 q = 1) (hb : d108443 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88858, d108443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10664 q ha hb
    | true =>
      simp only [d88858, d108443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d88859 q = 1) (hb : d108444 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88859, d108444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88859, d108444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88860 q = 1) (hb : d108445 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88860, d108445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88860, d108445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108446 q = 1) (hb : d142158 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108446, d142158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108446, d142158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d108447 q = 1) (hb : d142159 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108447, d142159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108447, d142159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108448 q = 1) (hb : d142160 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108448, d142160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108448, d142160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro32172 (p : Pattern) (ha : d108453 p = 1) (hb : d142164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108439 q = 1) (hb : d114787 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108439, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22944 q hb ha
    | true =>
      simp only [d108439, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108440 q = 1) (hb : d114788 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108440, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108440, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108441 q = 1) (hb : d114789 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108441, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108441, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88858 q = 1) (hb : d108443 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88858, d108443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10664 q ha hb
    | true =>
      simp only [d88858, d108443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88859 q = 1) (hb : d108444 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88859, d108444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88859, d108444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88860 q = 1) (hb : d108445 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88860, d108445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88860, d108445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108446 q = 1) (hb : d142158 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108446, d142158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108446, d142158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d88861 q = 1) (hb : d108451 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88861, d108451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d88861, d108451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d108452 q = 1) (hb : d142163 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108452, d142163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108452, d142163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108453 q = 1) (hb : d142164 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108453, d142164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108453, d142164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32173 (p : Pattern) (ha : d108459 p = 1) (hb : d142170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108449 q = 1) (hb : d142161 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108449, d142161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32171 q ha hb
    | true =>
      simp only [d108449, d142161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108450 q = 1) (hb : d142162 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108450, d142162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108450, d142162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108454 q = 1) (hb : d142165 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108454, d142165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32172 q ha hb
    | true =>
      simp only [d108454, d142165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108455 q = 1) (hb : d142166 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108455, d142166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108455, d142166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108456 q = 1) (hb : d142167 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108456, d142167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108456, d142167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108457 q = 1) (hb : d142168 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108457, d142168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108457, d142168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108458 q = 1) (hb : d142169 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108458, d142169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108458, d142169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108459 q = 1) (hb : d142170 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108459, d142170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108459, d142170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32174 (p : Pattern) (ha : d108461 p = 1) (hb : d142172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88858 q = 1) (hb : d108443 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88858, d108443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10664 q ha hb
    | true =>
      simp only [d88858, d108443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d88859 q = 1) (hb : d108444 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88859, d108444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88859, d108444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d88860 q = 1) (hb : d108445 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88860, d108445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88860, d108445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88861 q = 1) (hb : d108451 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88861, d108451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88861, d108451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108460 q = 1) (hb : d142171 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108460, d142171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108460, d142171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108461 q = 1) (hb : d142172 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108461, d142172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108461, d142172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32175 (p : Pattern) (ha : d108467 p = 1) (hb : d142178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108454 q = 1) (hb : d142165 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108454, d142165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32172 q ha hb
    | true =>
      simp only [d108454, d142165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108455 q = 1) (hb : d142166 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108455, d142166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108455, d142166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108462 q = 1) (hb : d142173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108462, d142173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32174 q ha hb
    | true =>
      simp only [d108462, d142173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108463 q = 1) (hb : d142174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108463, d142174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108463, d142174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108464 q = 1) (hb : d142175 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108464, d142175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108464, d142175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108465 q = 1) (hb : d142176 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108465, d142176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108465, d142176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108466 q = 1) (hb : d142177 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108466, d142177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108466, d142177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108467 q = 1) (hb : d142178 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108467, d142178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108467, d142178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32176 (p : Pattern) (ha : d108480 p = 1) (hb : d142164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108439 q = 1) (hb : d114787 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108439, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22944 q hb ha
    | true =>
      simp only [d108439, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108440 q = 1) (hb : d114788 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108440, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108440, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108441 q = 1) (hb : d114789 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108441, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108441, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88858 q = 1) (hb : d108443 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88858, d108443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10664 q ha hb
    | true =>
      simp only [d88858, d108443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88859 q = 1) (hb : d108444 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88859, d108444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88859, d108444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88860 q = 1) (hb : d108445 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88860, d108445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88860, d108445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108446 q = 1) (hb : d142158 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108446, d142158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108446, d142158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d88858 q = 1) (hb : d108475 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88858, d108475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22949 q ha hb
    | true =>
      simp only [d88858, d108475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d88859 q = 1) (hb : d108476 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88859, d108476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88859, d108476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88860 q = 1) (hb : d108477 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88860, d108477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88860, d108477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d88861 q = 1) (hb : d108478 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88861, d108478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88861, d108478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108479 q = 1) (hb : d142163 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108479, d142163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108479, d142163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d108480 q = 1) (hb : d142164 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108480, d142164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108480, d142164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro32177 (p : Pattern) (ha : d108486 p = 1) (hb : d142184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108481 q = 1) (hb : d142165 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108481, d142165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32176 q ha hb
    | true =>
      simp only [d108481, d142165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108482 q = 1) (hb : d142166 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108482, d142166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108482, d142166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108483 q = 1) (hb : d142181 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108483, d142181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108483, d142181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108484 q = 1) (hb : d142182 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108484, d142182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108484, d142182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108485 q = 1) (hb : d142183 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108485, d142183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108485, d142183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108486 q = 1) (hb : d142184 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108486, d142184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108486, d142184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32178 (p : Pattern) (ha : d108492 p = 1) (hb : d142190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108468 q = 1) (hb : d142179 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108468, d142179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32173 q ha hb
    | true =>
      simp only [d108468, d142179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32175 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108473 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108474 q = 1) (hb : d142180 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108474, d142180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108474, d142180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108487 q = 1) (hb : d142185 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108487, d142185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32177 q ha hb
    | true =>
      simp only [d108487, d142185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108488 q = 1) (hb : d142186 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108488, d142186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108488, d142186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108489 q = 1) (hb : d142187 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108489, d142187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108489, d142187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108490 q = 1) (hb : d142188 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108490, d142188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108490, d142188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108491 q = 1) (hb : d142189 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108491, d142189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108491, d142189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108492 q = 1) (hb : d142190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108492, d142190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108492, d142190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32179 (p : Pattern) (ha : d108472 p = 1) (hb : d142195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108462 q = 1) (hb : d142173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108462, d142173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32174 q ha hb
    | true =>
      simp only [d108462, d142173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108463 q = 1) (hb : d142174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108463, d142174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108463, d142174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108469 q = 1) (hb : d142192 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108469, d142192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108469, d142192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108470 q = 1) (hb : d142193 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108470, d142193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108470, d142193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108471 q = 1) (hb : d142194 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108471, d142194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108471, d142194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108472 q = 1) (hb : d142195 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108472, d142195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108472, d142195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32180 (p : Pattern) (ha : d108499 p = 1) (hb : d142201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108494 q = 1) (hb : d142196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108494, d142196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32179 q ha hb
    | true =>
      simp only [d108494, d142196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108495 q = 1) (hb : d142197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108495, d142197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108495, d142197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108496 q = 1) (hb : d142198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108496, d142198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108496, d142198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108497 q = 1) (hb : d142199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108497, d142199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108497, d142199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108498 q = 1) (hb : d142200 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108498, d142200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108498, d142200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108499 q = 1) (hb : d142201 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108499, d142201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108499, d142201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32181 (p : Pattern) (ha : d108505 p = 1) (hb : d142207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108326 q = 1) (hb : d142052 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108326, d142052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108326, d142052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32147 q ha hb
  have h2 (q : Pattern) (ha : d108327 q = 1) (hb : d142053 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108327, d142053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108327, d142053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108336 q = 1) (hb : d142062 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108336, d142062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32147 q ha hb
    | true =>
      simp only [d108336, d142062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32150 q ha hb
  have h4 (q : Pattern) (ha : d108337 q = 1) (hb : d142063 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108337, d142063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108337, d142063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108338 q = 1) (hb : d142064 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108338, d142064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108338, d142064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108409 q = 1) (hb : d142127 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108409, d142127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32159 q ha hb
    | true =>
      simp only [d108409, d142127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32166 q ha hb
  have h7 (q : Pattern) (ha : d108422 q = 1) (hb : d142140 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108422, d142140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32167 q ha hb
    | true =>
      simp only [d108422, d142140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32168 q ha hb
  have h8 (q : Pattern) (ha : d108423 q = 1) (hb : d142141 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108423, d142141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108423, d142141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108424 q = 1) (hb : d142142 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108424, d142142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108424, d142142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d108425 q = 1) (hb : d142143 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108425, d142143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108425, d142143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108429 q = 1) (hb : d142147 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108429, d142147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108429, d142147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32169 q ha hb
  have h12 (q : Pattern) (ha : d108431 q = 1) (hb : d142149 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108431, d142149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108431, d142149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32170 q ha hb
  have h13 (q : Pattern) (ha : d108432 q = 1) (hb : d142150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108432, d142150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108432, d142150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108433 q = 1) (hb : d142151 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108433, d142151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108433, d142151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d108434 q = 1) (hb : d142152 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108434, d142152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108434, d142152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d108435 q = 1) (hb : d142153 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108435, d142153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108435, d142153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108493 q = 1) (hb : d142191 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108493, d142191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108493, d142191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32178 q ha hb
  have h18 (q : Pattern) (ha : d108500 q = 1) (hb : d142202 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108500, d142202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108500, d142202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32180 q ha hb
  have h19 (q : Pattern) (ha : d108501 q = 1) (hb : d142203 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108501, d142203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108501, d142203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108502 q = 1) (hb : d142204 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108502, d142204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108502, d142204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d108503 q = 1) (hb : d142205 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108503, d142205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108503, d142205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d108504 q = 1) (hb : d142206 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108504, d142206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108504, d142206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d108505 q = 1) (hb : d142207 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108505, d142207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108505, d142207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro32182 (p : Pattern) (ha : d108511 p = 1) (hb : d142213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108506 q = 1) (hb : d142208 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108506, d142208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108506, d142208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32181 q ha hb
  have h2 (q : Pattern) (ha : d108507 q = 1) (hb : d142209 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108507, d142209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108507, d142209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108508 q = 1) (hb : d142210 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108508, d142210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108508, d142210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108509 q = 1) (hb : d142211 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108509, d142211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108509, d142211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108510 q = 1) (hb : d142212 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108510, d142212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108510, d142212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108511 q = 1) (hb : d142213 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108511, d142213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108511, d142213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32183 (p : Pattern) (ha : d108525 p = 1) (hb : d142220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108516 q = 1) (hb : d114875 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108516, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22962 q hb ha
    | true =>
      simp only [d108516, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108517 q = 1) (hb : d114876 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108517, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108517, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108518 q = 1) (hb : d114877 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108518, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108518, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88948 q = 1) (hb : d108519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88948, d108519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10677 q ha hb
    | true =>
      simp only [d88948, d108519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88949 q = 1) (hb : d108520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88949, d108520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88949, d108520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88950 q = 1) (hb : d108521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88950, d108521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88950, d108521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108522 q = 1) (hb : d142218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108522, d142218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108522, d142218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d88951 q = 1) (hb : d108523 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88951, d108523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d88951, d108523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d108524 q = 1) (hb : d142219 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108524, d142219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108524, d142219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108525 q = 1) (hb : d142220 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108525, d142220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108525, d142220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32184 (p : Pattern) (ha : d108529 p = 1) (hb : d142224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d88948 q = 1) (hb : d108519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88948, d108519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10677 q ha hb
    | true =>
      simp only [d88948, d108519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d88949 q = 1) (hb : d108520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88949, d108520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88949, d108520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d88950 q = 1) (hb : d108521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88950, d108521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88950, d108521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88951 q = 1) (hb : d108523 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88951, d108523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d88951, d108523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108528 q = 1) (hb : d142223 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108528, d142223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108528, d142223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108529 q = 1) (hb : d142224 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108529, d142224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108529, d142224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32185 (p : Pattern) (ha : d108535 p = 1) (hb : d142230 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108526 q = 1) (hb : d142221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32183 q ha hb
    | true =>
      simp only [d108526, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108527 q = 1) (hb : d142222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108530 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32184 q ha hb
    | true =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108531 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108532 q = 1) (hb : d142227 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108532, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108532, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108533 q = 1) (hb : d142228 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108533, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108533, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108534 q = 1) (hb : d142229 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108534, d142229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108534, d142229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108535 q = 1) (hb : d142230 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108535, d142230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108535, d142230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32186 (p : Pattern) (ha : d108539 p = 1) (hb : d142234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108530 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32184 q ha hb
    | true =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108531 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108536 q = 1) (hb : d142231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108536, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108536, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108537 q = 1) (hb : d142232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108537, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108537, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108538 q = 1) (hb : d142233 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108538, d142233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108538, d142233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108539 q = 1) (hb : d142234 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108539, d142234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108539, d142234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32187 (p : Pattern) (ha : d108545 p = 1) (hb : d142240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108540 q = 1) (hb : d142235 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108540, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32185 q ha hb
    | true =>
      simp only [d108540, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32186 q ha hb
  have h2 (q : Pattern) (ha : d108541 q = 1) (hb : d142236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108541, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108541, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108542 q = 1) (hb : d142237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108542, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108542, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108543 q = 1) (hb : d142238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108543, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108543, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108544 q = 1) (hb : d142239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108544, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108544, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108545 q = 1) (hb : d142240 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108545, d142240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108545, d142240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32188 (p : Pattern) (ha : d108548 p = 1) (hb : d142243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108526 q = 1) (hb : d142221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32183 q ha hb
    | true =>
      simp only [d108526, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108527 q = 1) (hb : d142222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108530 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32184 q ha hb
    | true =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108531 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108532 q = 1) (hb : d142227 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108532, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108532, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108533 q = 1) (hb : d142228 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108533, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108533, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108534 q = 1) (hb : d142229 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108534, d142229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108534, d142229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108548 q = 1) (hb : d142243 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108548, d142243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108548, d142243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32189 (p : Pattern) (ha : d108549 p = 1) (hb : d142244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108530 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32184 q ha hb
    | true =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108531 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108536 q = 1) (hb : d142231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108536, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108536, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108537 q = 1) (hb : d142232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108537, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108537, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108538 q = 1) (hb : d142233 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108538, d142233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108538, d142233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108549 q = 1) (hb : d142244 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108549, d142244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108549, d142244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32190 (p : Pattern) (ha : d108555 p = 1) (hb : d142250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108540 q = 1) (hb : d142235 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108540, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32185 q ha hb
    | true =>
      simp only [d108540, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32186 q ha hb
  have h2 (q : Pattern) (ha : d108541 q = 1) (hb : d142236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108541, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108541, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108542 q = 1) (hb : d142237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108542, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108542, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108543 q = 1) (hb : d142238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108543, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108543, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108544 q = 1) (hb : d142239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108544, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108544, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108550 q = 1) (hb : d142245 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108550, d142245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32188 q ha hb
    | true =>
      simp only [d108550, d142245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32189 q ha hb
  have h7 (q : Pattern) (ha : d108551 q = 1) (hb : d142246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108551, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108551, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108552 q = 1) (hb : d142247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108552, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108552, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108553 q = 1) (hb : d142248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108553, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108553, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108554 q = 1) (hb : d142249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108554, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108554, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108555 q = 1) (hb : d142250 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108555, d142250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108555, d142250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32191 (p : Pattern) (ha : d108560 p = 1) (hb : d142255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108526 q = 1) (hb : d142221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32183 q ha hb
    | true =>
      simp only [d108526, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108527 q = 1) (hb : d142222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108530 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32184 q ha hb
    | true =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108531 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108532 q = 1) (hb : d142227 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108532, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108532, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108533 q = 1) (hb : d142228 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108533, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108533, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108559 q = 1) (hb : d142254 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108559, d142254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108559, d142254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108560 q = 1) (hb : d142255 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108560, d142255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108560, d142255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32192 (p : Pattern) (ha : d108562 p = 1) (hb : d142257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108530 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32184 q ha hb
    | true =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108531 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108536 q = 1) (hb : d142231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108536, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108536, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108537 q = 1) (hb : d142232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108537, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108537, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108561 q = 1) (hb : d142256 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108561, d142256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108561, d142256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108562 q = 1) (hb : d142257 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108562, d142257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108562, d142257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32193 (p : Pattern) (ha : d108569 p = 1) (hb : d142264 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108526 q = 1) (hb : d142221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32183 q ha hb
    | true =>
      simp only [d108526, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108527 q = 1) (hb : d142222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108530 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32184 q ha hb
    | true =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108531 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108532 q = 1) (hb : d142227 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108532, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108532, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108567 q = 1) (hb : d142262 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108567, d142262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108567, d142262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108568 q = 1) (hb : d142263 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108568, d142263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108568, d142263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108569 q = 1) (hb : d142264 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108569, d142264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108569, d142264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32194 (p : Pattern) (ha : d108572 p = 1) (hb : d142267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108530 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32184 q ha hb
    | true =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108531 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108536 q = 1) (hb : d142231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108536, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108536, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108570 q = 1) (hb : d142265 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108570, d142265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108570, d142265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108571 q = 1) (hb : d142266 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108571, d142266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108571, d142266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108572 q = 1) (hb : d142267 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108572, d142267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108572, d142267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32195 (p : Pattern) (ha : d108581 p = 1) (hb : d142276 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108576 q = 1) (hb : d142271 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108576, d142271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28901 q hb ha
    | true =>
      simp only [d108576, d142271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108577 q = 1) (hb : d142272 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108577, d142272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108577, d142272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108578 q = 1) (hb : d142273 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108578, d142273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108578, d142273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108516 q = 1) (hb : d114875 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108516, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22962 q hb ha
    | true =>
      simp only [d108516, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108517 q = 1) (hb : d114876 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108517, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108517, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108518 q = 1) (hb : d114877 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108518, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108518, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108579 q = 1) (hb : d142274 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108579, d142274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108579, d142274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d88948 q = 1) (hb : d108519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88948, d108519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10677 q ha hb
    | true =>
      simp only [d88948, d108519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d88949 q = 1) (hb : d108520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88949, d108520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88949, d108520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88950 q = 1) (hb : d108521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88950, d108521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88950, d108521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108522 q = 1) (hb : d142218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108522, d142218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108522, d142218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d108580 q = 1) (hb : d142275 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108580, d142275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108580, d142275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108581 q = 1) (hb : d142276 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108581, d142276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108581, d142276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro32196 (p : Pattern) (ha : d108587 p = 1) (hb : d142282 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108582 q = 1) (hb : d142277 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108582, d142277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32195 q ha hb
    | true =>
      simp only [d108582, d142277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108583 q = 1) (hb : d142278 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108583, d142278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108583, d142278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108526 q = 1) (hb : d142221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32183 q ha hb
    | true =>
      simp only [d108526, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108527 q = 1) (hb : d142222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108584 q = 1) (hb : d142279 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108584, d142279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108584, d142279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108585 q = 1) (hb : d142280 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108585, d142280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108585, d142280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108586 q = 1) (hb : d142281 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108586, d142281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108586, d142281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108587 q = 1) (hb : d142282 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108587, d142282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108587, d142282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro32197 (p : Pattern) (ha : d108595 p = 1) (hb : d142220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108516 q = 1) (hb : d114875 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108516, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22962 q hb ha
    | true =>
      simp only [d108516, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108517 q = 1) (hb : d114876 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108517, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108517, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108518 q = 1) (hb : d114877 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108518, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108518, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88948 q = 1) (hb : d108519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88948, d108519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10677 q ha hb
    | true =>
      simp only [d88948, d108519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d88949 q = 1) (hb : d108520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88949, d108520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88949, d108520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d88950 q = 1) (hb : d108521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88950, d108521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88950, d108521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108522 q = 1) (hb : d142218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108522, d142218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108522, d142218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d88948 q = 1) (hb : d108590 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88948, d108590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22965 q ha hb
    | true =>
      simp only [d88948, d108590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d88949 q = 1) (hb : d108591 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88949, d108591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88949, d108591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d88950 q = 1) (hb : d108592 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88950, d108592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88950, d108592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d88951 q = 1) (hb : d108593 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88951, d108593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d88951, d108593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108594 q = 1) (hb : d142219 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108594, d142219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108594, d142219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d108595 q = 1) (hb : d142220 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108595, d142220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108595, d142220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro32198 (p : Pattern) (ha : d108601 p = 1) (hb : d142288 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108596 q = 1) (hb : d142221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108596, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32197 q ha hb
    | true =>
      simp only [d108596, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108597 q = 1) (hb : d142222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108597, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108597, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108598 q = 1) (hb : d142285 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108598, d142285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108598, d142285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108599 q = 1) (hb : d142286 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108599, d142286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108599, d142286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108600 q = 1) (hb : d142287 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108600, d142287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108600, d142287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108601 q = 1) (hb : d142288 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108601, d142288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108601, d142288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32199 (p : Pattern) (ha : d108607 p = 1) (hb : d142294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108563 q = 1) (hb : d142258 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108563, d142258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32191 q ha hb
    | true =>
      simp only [d108563, d142258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32192 q ha hb
  have h2 (q : Pattern) (ha : d108564 q = 1) (hb : d142259 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108564, d142259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108564, d142259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108565 q = 1) (hb : d142260 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108565, d142260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108565, d142260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108566 q = 1) (hb : d142261 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108566, d142261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108566, d142261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108573 q = 1) (hb : d142268 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108573, d142268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32193 q ha hb
    | true =>
      simp only [d108573, d142268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32194 q ha hb
  have h6 (q : Pattern) (ha : d108574 q = 1) (hb : d142269 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108574, d142269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108574, d142269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108575 q = 1) (hb : d142270 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108575, d142270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108575, d142270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108588 q = 1) (hb : d142283 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108588, d142283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32196 q ha hb
    | true =>
      simp only [d108588, d142283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32185 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108540 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d108589 q = 1) (hb : d142284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108589, d142284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108589, d142284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d108602 q = 1) (hb : d142289 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108602, d142289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32198 q ha hb
    | true =>
      simp only [d108602, d142289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108603 q = 1) (hb : d142290 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108603, d142290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108603, d142290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d108604 q = 1) (hb : d142291 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108604, d142291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108604, d142291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108605 q = 1) (hb : d142292 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108605, d142292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108605, d142292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108606 q = 1) (hb : d142293 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108606, d142293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108606, d142293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108607 q = 1) (hb : d142294 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108607, d142294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108607, d142294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro32200 (p : Pattern) (ha : d108608 p = 1) (hb : d142295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108526 q = 1) (hb : d142221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32183 q ha hb
    | true =>
      simp only [d108526, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108527 q = 1) (hb : d142222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108530 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32184 q ha hb
    | true =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108531 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108532 q = 1) (hb : d142227 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108532, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108532, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108533 q = 1) (hb : d142228 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108533, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108533, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108559 q = 1) (hb : d142254 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108559, d142254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108559, d142254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108608 q = 1) (hb : d142295 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108608, d142295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108608, d142295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32201 (p : Pattern) (ha : d108609 p = 1) (hb : d142296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108530 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32184 q ha hb
    | true =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108531 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108536 q = 1) (hb : d142231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108536, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108536, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108537 q = 1) (hb : d142232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108537, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108537, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108561 q = 1) (hb : d142256 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108561, d142256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108561, d142256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108609 q = 1) (hb : d142296 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108609, d142296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108609, d142296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32202 (p : Pattern) (ha : d108614 p = 1) (hb : d142301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108526 q = 1) (hb : d142221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32183 q ha hb
    | true =>
      simp only [d108526, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108527 q = 1) (hb : d142222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108530 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32184 q ha hb
    | true =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108531 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108532 q = 1) (hb : d142227 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108532, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108532, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108567 q = 1) (hb : d142262 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108567, d142262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108567, d142262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108568 q = 1) (hb : d142263 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108568, d142263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108568, d142263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108614 q = 1) (hb : d142301 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108614, d142301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108614, d142301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32203 (p : Pattern) (ha : d108615 p = 1) (hb : d142302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108530 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32184 q ha hb
    | true =>
      simp only [d108530, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108531 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108531, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108536 q = 1) (hb : d142231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108536, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108536, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108570 q = 1) (hb : d142265 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108570, d142265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108570, d142265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108571 q = 1) (hb : d142266 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108571, d142266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108571, d142266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108615 q = 1) (hb : d142302 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108615, d142302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108615, d142302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32204 (p : Pattern) (ha : d108619 p = 1) (hb : d142306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108582 q = 1) (hb : d142277 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108582, d142277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32195 q ha hb
    | true =>
      simp only [d108582, d142277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108583 q = 1) (hb : d142278 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108583, d142278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108583, d142278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108526 q = 1) (hb : d142221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108526, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32183 q ha hb
    | true =>
      simp only [d108526, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108527 q = 1) (hb : d142222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108527, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108527, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108584 q = 1) (hb : d142279 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108584, d142279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108584, d142279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108585 q = 1) (hb : d142280 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108585, d142280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108585, d142280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108586 q = 1) (hb : d142281 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108586, d142281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108586, d142281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108619 q = 1) (hb : d142306 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108619, d142306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108619, d142306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32205 (p : Pattern) (ha : d108622 p = 1) (hb : d142309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108596 q = 1) (hb : d142221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108596, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32197 q ha hb
    | true =>
      simp only [d108596, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108597 q = 1) (hb : d142222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108597, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108597, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108598 q = 1) (hb : d142285 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108598, d142285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108598, d142285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108599 q = 1) (hb : d142286 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108599, d142286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108599, d142286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108600 q = 1) (hb : d142287 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108600, d142287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108600, d142287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108622 q = 1) (hb : d142309 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108622, d142309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108622, d142309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32206 (p : Pattern) (ha : d108628 p = 1) (hb : d142315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108563 q = 1) (hb : d142258 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108563, d142258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32191 q ha hb
    | true =>
      simp only [d108563, d142258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32192 q ha hb
  have h2 (q : Pattern) (ha : d108564 q = 1) (hb : d142259 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108564, d142259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108564, d142259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108565 q = 1) (hb : d142260 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108565, d142260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108565, d142260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108566 q = 1) (hb : d142261 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108566, d142261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108566, d142261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108573 q = 1) (hb : d142268 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108573, d142268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32193 q ha hb
    | true =>
      simp only [d108573, d142268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32194 q ha hb
  have h6 (q : Pattern) (ha : d108574 q = 1) (hb : d142269 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108574, d142269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108574, d142269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108575 q = 1) (hb : d142270 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108575, d142270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108575, d142270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108588 q = 1) (hb : d142283 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108588, d142283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32196 q ha hb
    | true =>
      simp only [d108588, d142283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32185 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d108540 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d108589 q = 1) (hb : d142284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108589, d142284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108589, d142284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d108602 q = 1) (hb : d142289 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108602, d142289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32198 q ha hb
    | true =>
      simp only [d108602, d142289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d108603 q = 1) (hb : d142290 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108603, d142290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108603, d142290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d108604 q = 1) (hb : d142291 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108604, d142291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108604, d142291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108605 q = 1) (hb : d142292 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108605, d142292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108605, d142292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108606 q = 1) (hb : d142293 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108606, d142293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108606, d142293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108610 q = 1) (hb : d142297 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108610, d142297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32200 q ha hb
    | true =>
      simp only [d108610, d142297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32201 q ha hb
  have h17 (q : Pattern) (ha : d108611 q = 1) (hb : d142298 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108611, d142298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108611, d142298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108612 q = 1) (hb : d142299 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108612, d142299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108612, d142299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d108613 q = 1) (hb : d142300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108613, d142300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108613, d142300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108616 q = 1) (hb : d142303 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108616, d142303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32202 q ha hb
    | true =>
      simp only [d108616, d142303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32203 q ha hb
  have h21 (q : Pattern) (ha : d108617 q = 1) (hb : d142304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108617, d142304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108617, d142304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d108618 q = 1) (hb : d142305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108618, d142305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108618, d142305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d108620 q = 1) (hb : d142307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108620, d142307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32204 q ha hb
    | true =>
      simp only [d108620, d142307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32188 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d108550 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d108621 q = 1) (hb : d142308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108621, d142308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108621, d142308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d108623 q = 1) (hb : d142310 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108623, d142310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32205 q ha hb
    | true =>
      simp only [d108623, d142310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d108624 q = 1) (hb : d142311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108624, d142311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d108624, d142311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d108625 q = 1) (hb : d142312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108625, d142312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d108625, d142312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d108626 q = 1) (hb : d142313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108626, d142313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108626, d142313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d108627 q = 1) (hb : d142314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108627, d142314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108627, d142314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d108628 q = 1) (hb : d142315 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108628, d142315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108628, d142315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro32207 (p : Pattern) (ha : d108635 p = 1) (hb : d142322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108540 q = 1) (hb : d142235 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108540, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32185 q ha hb
    | true =>
      simp only [d108540, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32186 q ha hb
  have h2 (q : Pattern) (ha : d108541 q = 1) (hb : d142236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108541, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108541, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108542 q = 1) (hb : d142237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108542, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108542, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108543 q = 1) (hb : d142238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108543, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108543, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108544 q = 1) (hb : d142239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108544, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108544, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108630 q = 1) (hb : d142317 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108630, d142317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32186 q ha hb
    | true =>
      simp only [d108630, d142317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108631 q = 1) (hb : d142318 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108631, d142318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108631, d142318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108632 q = 1) (hb : d142319 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108632, d142319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108632, d142319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108633 q = 1) (hb : d142320 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108633, d142320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108633, d142320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108634 q = 1) (hb : d142321 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108634, d142321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108634, d142321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108635 q = 1) (hb : d142322 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108635, d142322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108635, d142322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32208 (p : Pattern) (ha : d108641 p = 1) (hb : d142328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108630 q = 1) (hb : d142317 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108630, d142317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32186 q ha hb
    | true =>
      simp only [d108630, d142317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108631 q = 1) (hb : d142318 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108631, d142318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108631, d142318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108632 q = 1) (hb : d142319 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108632, d142319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108632, d142319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108633 q = 1) (hb : d142320 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108633, d142320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108633, d142320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108634 q = 1) (hb : d142321 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108634, d142321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108634, d142321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108636 q = 1) (hb : d142323 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108636, d142323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32189 q ha hb
    | true =>
      simp only [d108636, d142323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108637 q = 1) (hb : d142324 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108637, d142324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108637, d142324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108638 q = 1) (hb : d142325 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108638, d142325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108638, d142325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d108639 q = 1) (hb : d142326 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108639, d142326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108639, d142326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108640 q = 1) (hb : d142327 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108640, d142327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108640, d142327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108641 q = 1) (hb : d142328 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108641, d142328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108641, d142328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro32209 (p : Pattern) (ha : d108648 p = 1) (hb : d142335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108620 q = 1) (hb : d142307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108620, d142307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32204 q ha hb
    | true =>
      simp only [d108620, d142307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32188 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108550 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108621 q = 1) (hb : d142308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108621, d142308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108621, d142308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108623 q = 1) (hb : d142310 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108623, d142310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32205 q ha hb
    | true =>
      simp only [d108623, d142310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108624 q = 1) (hb : d142311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108624, d142311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108624, d142311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108625 q = 1) (hb : d142312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108625, d142312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108625, d142312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108646 q = 1) (hb : d142333 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108646, d142333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108646, d142333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108647 q = 1) (hb : d142334 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108647, d142334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108647, d142334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108648 q = 1) (hb : d142335 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108648, d142335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108648, d142335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32210 (p : Pattern) (ha : d108650 p = 1) (hb : d142337 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108636 q = 1) (hb : d142323 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108636, d142323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32189 q ha hb
    | true =>
      simp only [d108636, d142323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108637 q = 1) (hb : d142324 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108637, d142324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108637, d142324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108638 q = 1) (hb : d142325 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108638, d142325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108638, d142325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108639 q = 1) (hb : d142326 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108639, d142326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108639, d142326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108640 q = 1) (hb : d142327 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108640, d142327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108640, d142327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108650 q = 1) (hb : d142337 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108650, d142337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108650, d142337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32211 (p : Pattern) (ha : d108668 p = 1) (hb : d142349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108656 q = 1) (hb : d142343 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108656, d142343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28918 q hb ha
    | true =>
      simp only [d108656, d142343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108657 q = 1) (hb : d142344 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108657, d142344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108657, d142344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108658 q = 1) (hb : d142345 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108658, d142345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108658, d142345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108659 q = 1) (hb : d114932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108659, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22976 q hb ha
    | true =>
      simp only [d108659, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108660 q = 1) (hb : d114933 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108660, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108660, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108661 q = 1) (hb : d114934 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108661, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108661, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108662 q = 1) (hb : d142346 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108662, d142346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108662, d142346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d89012 q = 1) (hb : d108663 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d89012, d108663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10696 q ha hb
    | true =>
      simp only [d89012, d108663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d89013 q = 1) (hb : d108664 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d89013, d108664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89013, d108664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d89014 q = 1) (hb : d108665 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d89014, d108665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89014, d108665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108666 q = 1) (hb : d142347 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108666, d142347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108666, d142347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d108667 q = 1) (hb : d142348 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108667, d142348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108667, d142348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108668 q = 1) (hb : d142349 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108668, d142349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108668, d142349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro32212 (p : Pattern) (ha : d108673 p = 1) (hb : d142353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108659 q = 1) (hb : d114932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108659, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22976 q hb ha
    | true =>
      simp only [d108659, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108660 q = 1) (hb : d114933 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108660, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108660, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108661 q = 1) (hb : d114934 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108661, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108661, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89012 q = 1) (hb : d108663 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d89012, d108663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10696 q ha hb
    | true =>
      simp only [d89012, d108663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89013 q = 1) (hb : d108664 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d89013, d108664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89013, d108664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89014 q = 1) (hb : d108665 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d89014, d108665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89014, d108665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108666 q = 1) (hb : d142347 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108666, d142347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108666, d142347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d89015 q = 1) (hb : d108671 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d89015, d108671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d89015, d108671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d108672 q = 1) (hb : d142352 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108672, d142352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108672, d142352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108673 q = 1) (hb : d142353 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108673, d142353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108673, d142353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro32213 (p : Pattern) (ha : d108679 p = 1) (hb : d142359 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108669 q = 1) (hb : d142350 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108669, d142350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32211 q ha hb
    | true =>
      simp only [d108669, d142350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108670 q = 1) (hb : d142351 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108670, d142351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108670, d142351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108674 q = 1) (hb : d142354 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108674, d142354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32212 q ha hb
    | true =>
      simp only [d108674, d142354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108675 q = 1) (hb : d142355 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108675, d142355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108675, d142355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108676 q = 1) (hb : d142356 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108676, d142356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108676, d142356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108677 q = 1) (hb : d142357 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108677, d142357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108677, d142357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108678 q = 1) (hb : d142358 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108678, d142358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108678, d142358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108679 q = 1) (hb : d142359 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108679, d142359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108679, d142359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32214 (p : Pattern) (ha : d108681 p = 1) (hb : d142361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d89012 q = 1) (hb : d108663 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d89012, d108663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10696 q ha hb
    | true =>
      simp only [d89012, d108663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d89013 q = 1) (hb : d108664 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d89013, d108664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89013, d108664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d89014 q = 1) (hb : d108665 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d89014, d108665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89014, d108665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89015 q = 1) (hb : d108671 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d89015, d108671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d89015, d108671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108680 q = 1) (hb : d142360 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108680, d142360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108680, d142360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108681 q = 1) (hb : d142361 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108681, d142361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108681, d142361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32215 (p : Pattern) (ha : d108687 p = 1) (hb : d142367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108674 q = 1) (hb : d142354 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108674, d142354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32212 q ha hb
    | true =>
      simp only [d108674, d142354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108675 q = 1) (hb : d142355 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108675, d142355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108675, d142355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108682 q = 1) (hb : d142362 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108682, d142362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32214 q ha hb
    | true =>
      simp only [d108682, d142362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108683 q = 1) (hb : d142363 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108683, d142363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108683, d142363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108684 q = 1) (hb : d142364 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108684, d142364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108684, d142364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108685 q = 1) (hb : d142365 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108685, d142365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108685, d142365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d108686 q = 1) (hb : d142366 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108686, d142366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108686, d142366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d108687 q = 1) (hb : d142367 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108687, d142367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108687, d142367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32216 (p : Pattern) (ha : d108700 p = 1) (hb : d142353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108659 q = 1) (hb : d114932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d108659, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22976 q hb ha
    | true =>
      simp only [d108659, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108660 q = 1) (hb : d114933 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d108660, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108660, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108661 q = 1) (hb : d114934 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d108661, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108661, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89012 q = 1) (hb : d108663 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d89012, d108663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10696 q ha hb
    | true =>
      simp only [d89012, d108663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d89013 q = 1) (hb : d108664 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d89013, d108664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89013, d108664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89014 q = 1) (hb : d108665 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d89014, d108665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89014, d108665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108666 q = 1) (hb : d142347 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d108666, d142347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108666, d142347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d89012 q = 1) (hb : d108695 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d89012, d108695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22981 q ha hb
    | true =>
      simp only [d89012, d108695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d89013 q = 1) (hb : d108696 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d89013, d108696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89013, d108696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d89014 q = 1) (hb : d108697 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d89014, d108697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89014, d108697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d89015 q = 1) (hb : d108698 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d89015, d108698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d89015, d108698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d108699 q = 1) (hb : d142352 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d108699, d142352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108699, d142352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d108700 q = 1) (hb : d142353 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d108700, d142353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108700, d142353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro32217 (p : Pattern) (ha : d108706 p = 1) (hb : d142373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108701 q = 1) (hb : d142354 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108701, d142354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32216 q ha hb
    | true =>
      simp only [d108701, d142354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108702 q = 1) (hb : d142355 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108702, d142355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108702, d142355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108703 q = 1) (hb : d142370 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108703, d142370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108703, d142370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108704 q = 1) (hb : d142371 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108704, d142371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108704, d142371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108705 q = 1) (hb : d142372 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108705, d142372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108705, d142372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108706 q = 1) (hb : d142373 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108706, d142373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108706, d142373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32218 (p : Pattern) (ha : d108712 p = 1) (hb : d142379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108688 q = 1) (hb : d142368 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108688, d142368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32213 q ha hb
    | true =>
      simp only [d108688, d142368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32215 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d108693 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108694 q = 1) (hb : d142369 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108694, d142369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108694, d142369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d108707 q = 1) (hb : d142374 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108707, d142374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32217 q ha hb
    | true =>
      simp only [d108707, d142374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108708 q = 1) (hb : d142375 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108708, d142375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108708, d142375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108709 q = 1) (hb : d142376 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108709, d142376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108709, d142376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108710 q = 1) (hb : d142377 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108710, d142377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108710, d142377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108711 q = 1) (hb : d142378 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108711, d142378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108711, d142378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108712 q = 1) (hb : d142379 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108712, d142379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108712, d142379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro32219 (p : Pattern) (ha : d108692 p = 1) (hb : d142384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108682 q = 1) (hb : d142362 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d108682, d142362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32214 q ha hb
    | true =>
      simp only [d108682, d142362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108683 q = 1) (hb : d142363 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d108683, d142363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108683, d142363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108689 q = 1) (hb : d142381 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d108689, d142381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108689, d142381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108690 q = 1) (hb : d142382 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d108690, d142382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108690, d142382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108691 q = 1) (hb : d142383 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d108691, d142383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108691, d142383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108692 q = 1) (hb : d142384 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d108692, d142384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108692, d142384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32220 (p : Pattern) (ha : d108719 p = 1) (hb : d142390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108714 q = 1) (hb : d142385 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d108714, d142385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32219 q ha hb
    | true =>
      simp only [d108714, d142385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108715 q = 1) (hb : d142386 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108715, d142386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108715, d142386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108716 q = 1) (hb : d142387 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108716, d142387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108716, d142387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108717 q = 1) (hb : d142388 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108717, d142388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108717, d142388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108718 q = 1) (hb : d142389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108718, d142389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108718, d142389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108719 q = 1) (hb : d142390 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108719, d142390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108719, d142390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32221 (p : Pattern) (ha : d108725 p = 1) (hb : d142396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108546 q = 1) (hb : d142241 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108546, d142241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108546, d142241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32187 q ha hb
  have h2 (q : Pattern) (ha : d108547 q = 1) (hb : d142242 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108547, d142242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108547, d142242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108556 q = 1) (hb : d142251 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108556, d142251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32187 q ha hb
    | true =>
      simp only [d108556, d142251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32190 q ha hb
  have h4 (q : Pattern) (ha : d108557 q = 1) (hb : d142252 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108557, d142252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108557, d142252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108558 q = 1) (hb : d142253 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108558, d142253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108558, d142253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108629 q = 1) (hb : d142316 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108629, d142316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32199 q ha hb
    | true =>
      simp only [d108629, d142316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32206 q ha hb
  have h7 (q : Pattern) (ha : d108642 q = 1) (hb : d142329 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108642, d142329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32207 q ha hb
    | true =>
      simp only [d108642, d142329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32208 q ha hb
  have h8 (q : Pattern) (ha : d108643 q = 1) (hb : d142330 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108643, d142330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108643, d142330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108644 q = 1) (hb : d142331 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108644, d142331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108644, d142331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d108645 q = 1) (hb : d142332 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108645, d142332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108645, d142332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108649 q = 1) (hb : d142336 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108649, d142336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108649, d142336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32209 q ha hb
  have h12 (q : Pattern) (ha : d108651 q = 1) (hb : d142338 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108651, d142338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108651, d142338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32210 q ha hb
  have h13 (q : Pattern) (ha : d108652 q = 1) (hb : d142339 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108652, d142339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108652, d142339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108653 q = 1) (hb : d142340 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108653, d142340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108653, d142340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d108654 q = 1) (hb : d142341 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108654, d142341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108654, d142341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d108655 q = 1) (hb : d142342 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108655, d142342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108655, d142342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108713 q = 1) (hb : d142380 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108713, d142380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108713, d142380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32218 q ha hb
  have h18 (q : Pattern) (ha : d108720 q = 1) (hb : d142391 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108720, d142391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108720, d142391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32220 q ha hb
  have h19 (q : Pattern) (ha : d108721 q = 1) (hb : d142392 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108721, d142392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108721, d142392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d108722 q = 1) (hb : d142393 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108722, d142393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108722, d142393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d108723 q = 1) (hb : d142394 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108723, d142394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108723, d142394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d108724 q = 1) (hb : d142395 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108724, d142395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108724, d142395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d108725 q = 1) (hb : d142396 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108725, d142396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108725, d142396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro32222 (p : Pattern) (ha : d108731 p = 1) (hb : d142402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108726 q = 1) (hb : d142397 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108726, d142397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108726, d142397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32221 q ha hb
  have h2 (q : Pattern) (ha : d108727 q = 1) (hb : d142398 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108727, d142398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108727, d142398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108728 q = 1) (hb : d142399 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108728, d142399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108728, d142399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108729 q = 1) (hb : d142400 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108729, d142400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108729, d142400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108730 q = 1) (hb : d142401 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108730, d142401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108730, d142401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108731 q = 1) (hb : d142402 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108731, d142402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108731, d142402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32223 (p : Pattern) (ha : d108737 p = 1) (hb : d142408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d107858 q = 1) (hb : d141653 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d107858, d141653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32024 q ha hb
    | true =>
      simp only [d107858, d141653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32062 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108075 q = 1) (hb : d141839 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108075, d141839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108075, d141839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32102 q ha hb
  have h3 (q : Pattern) (ha : d108076 q = 1) (hb : d141840 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108076, d141840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108076, d141840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108293 q = 1) (hb : d142026 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108293, d142026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108293, d142026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32142 q ha hb
  have h5 (q : Pattern) (ha : d108294 q = 1) (hb : d142027 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108294, d142027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108294, d142027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108295 q = 1) (hb : d142028 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108295, d142028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108295, d142028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108512 q = 1) (hb : d142214 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108512, d142214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108512, d142214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32182 q ha hb
  have h8 (q : Pattern) (ha : d108513 q = 1) (hb : d142215 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108513, d142215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108513, d142215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108514 q = 1) (hb : d142216 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108514, d142216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108514, d142216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108515 q = 1) (hb : d142217 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d108515, d142217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108515, d142217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108732 q = 1) (hb : d142403 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108732, d142403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108732, d142403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32222 q ha hb
  have h12 (q : Pattern) (ha : d108733 q = 1) (hb : d142404 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108733, d142404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108733, d142404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d108734 q = 1) (hb : d142405 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108734, d142405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108734, d142405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108735 q = 1) (hb : d142406 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d108735, d142406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108735, d142406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108736 q = 1) (hb : d142407 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d108736, d142407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108736, d142407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108737 q = 1) (hb : d142408 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d108737, d142408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108737, d142408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro32224 (p : Pattern) (ha : d108743 p = 1) (hb : d142414 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108738 q = 1) (hb : d142409 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d108738, d142409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32223 q ha hb
    | true =>
      simp only [d108738, d142409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108739 q = 1) (hb : d142410 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d108739, d142410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108739, d142410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108740 q = 1) (hb : d142411 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d108740, d142411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108740, d142411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108741 q = 1) (hb : d142412 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d108741, d142412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108741, d142412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108742 q = 1) (hb : d142413 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d108742, d142413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108742, d142413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108743 q = 1) (hb : d142414 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d108743, d142414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108743, d142414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32225 (p : Pattern) (ha : d108749 p = 1) (hb : d142420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108744 q = 1) (hb : d142415 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d108744, d142415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32224 q ha hb
    | true =>
      simp only [d108744, d142415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108745 q = 1) (hb : d142416 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d108745, d142416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108745, d142416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108746 q = 1) (hb : d142417 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d108746, d142417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108746, d142417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108747 q = 1) (hb : d142418 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d108747, d142418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108747, d142418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108748 q = 1) (hb : d142419 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d108748, d142419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108748, d142419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108749 q = 1) (hb : d142420 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d108749, d142420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108749, d142420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32226 (p : Pattern) (ha : d108755 p = 1) (hb : d142426 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108750 q = 1) (hb : d142421 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d108750, d142421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32225 q ha hb
    | true =>
      simp only [d108750, d142421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108751 q = 1) (hb : d142422 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d108751, d142422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108751, d142422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108752 q = 1) (hb : d142423 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d108752, d142423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108752, d142423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108753 q = 1) (hb : d142424 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d108753, d142424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108753, d142424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108754 q = 1) (hb : d142425 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d108754, d142425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108754, d142425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108755 q = 1) (hb : d142426 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d108755, d142426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108755, d142426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32227 (p : Pattern) (ha : d108761 p = 1) (hb : d142432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108756 q = 1) (hb : d142427 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d108756, d142427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32226 q ha hb
    | true =>
      simp only [d108756, d142427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108757 q = 1) (hb : d142428 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d108757, d142428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108757, d142428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108758 q = 1) (hb : d142429 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d108758, d142429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108758, d142429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108759 q = 1) (hb : d142430 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d108759, d142430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108759, d142430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108760 q = 1) (hb : d142431 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d108760, d142431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108760, d142431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108761 q = 1) (hb : d142432 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d108761, d142432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108761, d142432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32228 (p : Pattern) (ha : d108767 p = 1) (hb : d142438 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108762 q = 1) (hb : d142433 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d108762, d142433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32227 q ha hb
    | true =>
      simp only [d108762, d142433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108763 q = 1) (hb : d142434 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d108763, d142434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108763, d142434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108764 q = 1) (hb : d142435 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d108764, d142435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108764, d142435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108765 q = 1) (hb : d142436 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d108765, d142436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108765, d142436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108766 q = 1) (hb : d142437 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d108766, d142437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108766, d142437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108767 q = 1) (hb : d142438 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d108767, d142438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108767, d142438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32229 (p : Pattern) (ha : d108773 p = 1) (hb : d142444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108768 q = 1) (hb : d142439 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d108768, d142439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32228 q ha hb
    | true =>
      simp only [d108768, d142439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108769 q = 1) (hb : d142440 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d108769, d142440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108769, d142440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108770 q = 1) (hb : d142441 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d108770, d142441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108770, d142441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108771 q = 1) (hb : d142442 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d108771, d142442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108771, d142442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108772 q = 1) (hb : d142443 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d108772, d142443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108772, d142443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108773 q = 1) (hb : d142444 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d108773, d142444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108773, d142444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32230 (p : Pattern) (ha : d108779 p = 1) (hb : d142450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108774 q = 1) (hb : d142445 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d108774, d142445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32229 q ha hb
    | true =>
      simp only [d108774, d142445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d108775 q = 1) (hb : d142446 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d108775, d142446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108775, d142446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d108776 q = 1) (hb : d142447 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d108776, d142447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108776, d142447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d108777 q = 1) (hb : d142448 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d108777, d142448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108777, d142448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d108778 q = 1) (hb : d142449 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d108778, d142449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108778, d142449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d108779 q = 1) (hb : d142450 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d108779, d142450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108779, d142450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro32231 (p : Pattern) (ha : d112686 p = 1) (hb : d150329 p = 1) : d142453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d112686 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12241 q = 1) (hb : d112686 q = 1) : d141318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31756 q ha hb
    | true =>
      simp only [d12241, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12292 q = 1) (hb : d112686 q = 1) : d141369 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12292, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12293 q = 1) (hb : d112686 q = 1) : d141370 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12293, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12294 q = 1) (hb : d112686 q = 1) : d141371 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12294, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12295 q = 1) (hb : d112686 q = 1) : d141372 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12295, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112686 q = 1) (hb : d150329 q = 1) : d142453 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150329, d142453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150329, d142453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro32232 (p : Pattern) (ha : d112686 p = 1) (hb : d150339 p = 1) : d142463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d112686 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12268 q = 1) (hb : d112686 q = 1) : d141345 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12268, d141345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31760 q ha hb
    | true =>
      simp only [d12268, d141345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150335 q = 1) : d142459 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150335, d142459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150335, d142459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150336 q = 1) : d142460 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150336, d142460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150336, d142460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150337 q = 1) : d142461 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150337, d142461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150337, d142461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150338 q = 1) : d142462 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150338, d142462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150338, d142462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112686 q = 1) (hb : d150339 q = 1) : d142463 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150339, d142463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150339, d142463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32233 (p : Pattern) (ha : d112686 p = 1) (hb : d150345 p = 1) : d142469 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12297 q = 1) (hb : d112686 q = 1) : d141374 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12297, d141374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31763 q ha hb
    | true =>
      simp only [d12297, d141374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31764 q ha hb
  have h2 (q : Pattern) (ha : d12298 q = 1) (hb : d112686 q = 1) : d141375 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12298, d141375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12298, d141375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150327 q = 1) : d142451 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150327, d142451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150327, d142451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150328 q = 1) : d142452 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150328, d142452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150328, d142452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150330 q = 1) : d142454 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150330, d142454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150330, d142454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32231 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150331 q = 1) : d142455 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150331, d142455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150331, d142455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112686 q = 1) (hb : d150332 q = 1) : d142456 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150332, d142456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150332, d142456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112686 q = 1) (hb : d150333 q = 1) : d142457 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150333, d142457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150333, d142457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d112686 q = 1) (hb : d150334 q = 1) : d142458 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150334, d142458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150334, d142458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112686 q = 1) (hb : d150340 q = 1) : d142464 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150340, d142464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150340, d142464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32232 q ha hb
  have h11 (q : Pattern) (ha : d112686 q = 1) (hb : d150341 q = 1) : d142465 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150341, d142465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150341, d142465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d112686 q = 1) (hb : d150342 q = 1) : d142466 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150342, d142466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150342, d142466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112686 q = 1) (hb : d150343 q = 1) : d142467 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150343, d142467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150343, d142467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d112686 q = 1) (hb : d150344 q = 1) : d142468 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150344, d142468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150344, d142468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d112686 q = 1) (hb : d150345 q = 1) : d142469 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150345, d142469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150345, d142469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32234 (p : Pattern) (ha : d112686 p = 1) (hb : d150351 p = 1) : d142475 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d112686 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112686 q = 1) (hb : d150346 q = 1) : d142470 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150346, d142470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150346, d142470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32233 q ha hb
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150347 q = 1) : d142471 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150347, d142471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150347, d142471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150348 q = 1) : d142472 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150348, d142472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150348, d142472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150349 q = 1) : d142473 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150349, d142473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150349, d142473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150350 q = 1) : d142474 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150350, d142474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150350, d142474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112686 q = 1) (hb : d150351 q = 1) : d142475 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150351, d142475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150351, d142475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro32235 (p : Pattern) (ha : d112686 p = 1) (hb : d150354 p = 1) : d142478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12463 q = 1) (hb : d112686 q = 1) : d141502 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12463, d141502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31789 q ha hb
    | true =>
      simp only [d12463, d141502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31790 q ha hb
  have h2 (q : Pattern) (ha : d12464 q = 1) (hb : d112686 q = 1) : d141503 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12464, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12464, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12465 q = 1) (hb : d112686 q = 1) : d141504 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12465, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12465, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12466 q = 1) (hb : d112686 q = 1) : d141505 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12466, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12466, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12467 q = 1) (hb : d112686 q = 1) : d141506 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12467, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12467, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150354 q = 1) : d142478 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150354, d142478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150354, d142478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro32236 (p : Pattern) (ha : d112686 p = 1) (hb : d150365 p = 1) : d142489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112686 q = 1) (hb : d150360 q = 1) : d142484 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150360, d142484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31817 q hb ha
    | true =>
      simp only [d150360, d142484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31796 q hb ha
  have h2 (q : Pattern) (ha : d112686 q = 1) (hb : d150361 q = 1) : d142485 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150361, d142485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150361, d142485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150362 q = 1) : d142486 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150362, d142486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150362, d142486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150363 q = 1) : d142487 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150363, d142487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150363, d142487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150364 q = 1) : d142488 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150364, d142488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150364, d142488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150365 q = 1) : d142489 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150365, d142489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150365, d142489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32237 (p : Pattern) (ha : d112686 p = 1) (hb : d150371 p = 1) : d142495 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12469 q = 1) (hb : d112686 q = 1) : d141508 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12469, d141508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31788 q ha hb
    | true =>
      simp only [d12469, d141508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31791 q ha hb
  have h2 (q : Pattern) (ha : d12470 q = 1) (hb : d112686 q = 1) : d141509 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12470, d141509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12470, d141509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150352 q = 1) : d142476 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150352, d142476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150352, d142476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150353 q = 1) : d142477 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150353, d142477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150353, d142477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150355 q = 1) : d142479 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150355, d142479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150355, d142479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32235 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150356 q = 1) : d142480 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150356, d142480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150356, d142480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112686 q = 1) (hb : d150357 q = 1) : d142481 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150357, d142481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150357, d142481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112686 q = 1) (hb : d150358 q = 1) : d142482 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150358, d142482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150358, d142482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d112686 q = 1) (hb : d150359 q = 1) : d142483 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150359, d142483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150359, d142483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112686 q = 1) (hb : d150366 q = 1) : d142490 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150366, d142490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150366, d142490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32236 q ha hb
  have h11 (q : Pattern) (ha : d112686 q = 1) (hb : d150367 q = 1) : d142491 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150367, d142491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150367, d142491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d112686 q = 1) (hb : d150368 q = 1) : d142492 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150368, d142492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150368, d142492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112686 q = 1) (hb : d150369 q = 1) : d142493 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150369, d142493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150369, d142493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d112686 q = 1) (hb : d150370 q = 1) : d142494 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150370, d142494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150370, d142494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d112686 q = 1) (hb : d150371 q = 1) : d142495 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150371, d142495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150371, d142495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32238 (p : Pattern) (ha : d112686 p = 1) (hb : d150377 p = 1) : d142501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112686 q = 1) (hb : d150372 q = 1) : d142496 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150372, d142496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150372, d142496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32237 q ha hb
  have h2 (q : Pattern) (ha : d112686 q = 1) (hb : d150373 q = 1) : d142497 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150373, d142497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150373, d142497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150374 q = 1) : d142498 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150374, d142498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150374, d142498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150375 q = 1) : d142499 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150375, d142499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150375, d142499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150376 q = 1) : d142500 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150376, d142500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150376, d142500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150377 q = 1) : d142501 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150377, d142501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150377, d142501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32239 (p : Pattern) (ha : d112686 p = 1) (hb : d150381 p = 1) : d142505 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12718 q = 1) (hb : d112686 q = 1) : d141681 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12718, d141681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31827 q ha hb
    | true =>
      simp only [d12718, d141681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31828 q ha hb
  have h2 (q : Pattern) (ha : d12719 q = 1) (hb : d112686 q = 1) : d141682 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12719, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12719, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12720 q = 1) (hb : d112686 q = 1) : d141683 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12720, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12720, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12721 q = 1) (hb : d112686 q = 1) : d141684 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12721, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12721, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12722 q = 1) (hb : d112686 q = 1) : d141685 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12722, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12722, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150381 q = 1) : d142505 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150381, d142505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150381, d142505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro32240 (p : Pattern) (ha : d112686 p = 1) (hb : d150392 p = 1) : d142516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112686 q = 1) (hb : d150387 q = 1) : d142511 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150387, d142511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31855 q hb ha
    | true =>
      simp only [d150387, d142511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31834 q hb ha
  have h2 (q : Pattern) (ha : d112686 q = 1) (hb : d150388 q = 1) : d142512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150388, d142512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150388, d142512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150389 q = 1) : d142513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150389, d142513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150389, d142513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150390 q = 1) : d142514 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150390, d142514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150390, d142514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150391 q = 1) : d142515 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150391, d142515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150391, d142515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150392 q = 1) : d142516 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150392, d142516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150392, d142516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32241 (p : Pattern) (ha : d112686 p = 1) (hb : d150398 p = 1) : d142522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12724 q = 1) (hb : d112686 q = 1) : d141687 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12724, d141687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31826 q ha hb
    | true =>
      simp only [d12724, d141687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31829 q ha hb
  have h2 (q : Pattern) (ha : d12725 q = 1) (hb : d112686 q = 1) : d141688 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12725, d141688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12725, d141688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150379 q = 1) : d142503 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150379, d142503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150379, d142503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150380 q = 1) : d142504 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150380, d142504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150380, d142504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150382 q = 1) : d142506 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150382, d142506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150382, d142506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32239 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150383 q = 1) : d142507 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150383, d142507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150383, d142507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112686 q = 1) (hb : d150384 q = 1) : d142508 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150384, d142508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150384, d142508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112686 q = 1) (hb : d150385 q = 1) : d142509 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150385, d142509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150385, d142509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d112686 q = 1) (hb : d150386 q = 1) : d142510 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150386, d142510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150386, d142510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112686 q = 1) (hb : d150393 q = 1) : d142517 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150393, d142517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150393, d142517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32240 q ha hb
  have h11 (q : Pattern) (ha : d112686 q = 1) (hb : d150394 q = 1) : d142518 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150394, d142518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150394, d142518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d112686 q = 1) (hb : d150395 q = 1) : d142519 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150395, d142519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150395, d142519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112686 q = 1) (hb : d150396 q = 1) : d142520 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150396, d142520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150396, d142520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d112686 q = 1) (hb : d150397 q = 1) : d142521 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150397, d142521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150397, d142521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d112686 q = 1) (hb : d150398 q = 1) : d142522 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150398, d142522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150398, d142522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32242 (p : Pattern) (ha : d112686 p = 1) (hb : d150404 p = 1) : d142528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112686 q = 1) (hb : d150399 q = 1) : d142523 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150399, d142523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150399, d142523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32241 q ha hb
  have h2 (q : Pattern) (ha : d112686 q = 1) (hb : d150400 q = 1) : d142524 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150400, d142524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150400, d142524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150401 q = 1) : d142525 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150401, d142525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150401, d142525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150402 q = 1) : d142526 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150402, d142526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150402, d142526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150403 q = 1) : d142527 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150403, d142527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150403, d142527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150404 q = 1) : d142528 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150404, d142528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150404, d142528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32243 (p : Pattern) (ha : d112686 p = 1) (hb : d150409 p = 1) : d142533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12992 q = 1) (hb : d112686 q = 1) : d141868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12992, d141868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31865 q ha hb
    | true =>
      simp only [d12992, d141868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31866 q ha hb
  have h2 (q : Pattern) (ha : d12993 q = 1) (hb : d112686 q = 1) : d141869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12993, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12993, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12994 q = 1) (hb : d112686 q = 1) : d141870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12994, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12994, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12995 q = 1) (hb : d112686 q = 1) : d141871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12995, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12995, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12996 q = 1) (hb : d112686 q = 1) : d141872 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12996, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12996, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150409 q = 1) : d142533 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150409, d142533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150409, d142533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro32244 (p : Pattern) (ha : d112686 p = 1) (hb : d150418 p = 1) : d141990 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13244 q = 1) (hb : d112686 q = 1) : d141977 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13244, d141977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31897 q ha hb
    | true =>
      simp only [d13244, d141977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13245 q = 1) (hb : d112686 q = 1) : d141978 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13245, d141978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13245, d141978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13197 q = 1) (hb : d112686 q = 1) : d141985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, d141985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31873 q ha hb
    | true =>
      simp only [d13197, d141985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13198 q = 1) (hb : d112686 q = 1) : d141986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, d141986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, d141986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150415 q = 1) : d141987 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150415, d141987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150415, d141987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150416 q = 1) : d141988 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150416, d141988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150416, d141988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112686 q = 1) (hb : d150417 q = 1) : d141989 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150417, d141989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150417, d141989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112686 q = 1) (hb : d150418 q = 1) : d141990 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150418, d141990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150418, d141990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro32245 (p : Pattern) (ha : d112686 p = 1) (hb : d150424 p = 1) : d142544 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112686 q = 1) (hb : d150419 q = 1) : d142539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150419, d142539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32244 q ha hb
    | true =>
      simp only [d150419, d142539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31874 q hb ha
  have h2 (q : Pattern) (ha : d112686 q = 1) (hb : d150420 q = 1) : d142540 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150420, d142540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150420, d142540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150421 q = 1) : d142541 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150421, d142541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150421, d142541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150422 q = 1) : d142542 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150422, d142542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150422, d142542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150423 q = 1) : d142543 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150423, d142543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150423, d142543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150424 q = 1) : d142544 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150424, d142544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150424, d142544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32246 (p : Pattern) (ha : d112686 p = 1) (hb : d150430 p = 1) : d142550 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12998 q = 1) (hb : d112686 q = 1) : d141874 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12998, d141874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31864 q ha hb
    | true =>
      simp only [d12998, d141874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31867 q ha hb
  have h2 (q : Pattern) (ha : d12999 q = 1) (hb : d112686 q = 1) : d141875 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12999, d141875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12999, d141875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150407 q = 1) : d142531 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150407, d142531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150407, d142531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150408 q = 1) : d142532 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150408, d142532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150408, d142532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150410 q = 1) : d142534 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150410, d142534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150410, d142534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32243 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150411 q = 1) : d142535 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150411, d142535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150411, d142535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112686 q = 1) (hb : d150412 q = 1) : d142536 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150412, d142536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150412, d142536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112686 q = 1) (hb : d150413 q = 1) : d142537 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150413, d142537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150413, d142537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d112686 q = 1) (hb : d150414 q = 1) : d142538 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150414, d142538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150414, d142538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112686 q = 1) (hb : d150425 q = 1) : d142545 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150425, d142545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150425, d142545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32245 q ha hb
  have h11 (q : Pattern) (ha : d112686 q = 1) (hb : d150426 q = 1) : d142546 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150426, d142546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150426, d142546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d112686 q = 1) (hb : d150427 q = 1) : d142547 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150427, d142547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150427, d142547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112686 q = 1) (hb : d150428 q = 1) : d142548 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150428, d142548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150428, d142548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d112686 q = 1) (hb : d150429 q = 1) : d142549 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150429, d142549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150429, d142549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d112686 q = 1) (hb : d150430 q = 1) : d142550 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150430, d142550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150430, d142550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro32247 (p : Pattern) (ha : d112686 p = 1) (hb : d150436 p = 1) : d142556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112686 q = 1) (hb : d150431 q = 1) : d142551 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150431, d142551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150431, d142551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32246 q ha hb
  have h2 (q : Pattern) (ha : d112686 q = 1) (hb : d150432 q = 1) : d142552 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150432, d142552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150432, d142552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112686 q = 1) (hb : d150433 q = 1) : d142553 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150433, d142553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150433, d142553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112686 q = 1) (hb : d150434 q = 1) : d142554 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150434, d142554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150434, d142554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150435 q = 1) : d142555 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150435, d142555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150435, d142555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150436 q = 1) : d142556 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150436, d142556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150436, d142556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro32248 (p : Pattern) (ha : d112686 p = 1) (hb : d150442 p = 1) : d142562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13318 q = 1) (hb : d112686 q = 1) : d142056 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13318, d142056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31907 q ha hb
    | true =>
      simp only [d13318, d142056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31908 q ha hb
  have h2 (q : Pattern) (ha : d13319 q = 1) (hb : d112686 q = 1) : d142057 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13319, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13319, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13320 q = 1) (hb : d112686 q = 1) : d142058 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13320, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13320, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13321 q = 1) (hb : d112686 q = 1) : d142059 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13321, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13321, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13322 q = 1) (hb : d112686 q = 1) : d142060 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13322, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13322, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150442 q = 1) : d142562 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150442, d142562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150442, d142562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro32249 (p : Pattern) (ha : d112686 p = 1) (hb : d150451 p = 1) : d142178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13570 q = 1) (hb : d112686 q = 1) : d142165 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13570, d142165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31939 q ha hb
    | true =>
      simp only [d13570, d142165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13571 q = 1) (hb : d112686 q = 1) : d142166 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13571, d142166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13571, d142166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13523 q = 1) (hb : d112686 q = 1) : d142173 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, d142173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31915 q ha hb
    | true =>
      simp only [d13523, d142173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13524 q = 1) (hb : d112686 q = 1) : d142174 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, d142174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, d142174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112686 q = 1) (hb : d150448 q = 1) : d142175 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150448, d142175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150448, d142175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112686 q = 1) (hb : d150449 q = 1) : d142176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150449, d142176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150449, d142176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112686 q = 1) (hb : d150450 q = 1) : d142177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150450, d142177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150450, d142177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112686 q = 1) (hb : d150451 q = 1) : d142178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150451, d142178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150451, d142178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
end NetHack.Soko22Hazard87
